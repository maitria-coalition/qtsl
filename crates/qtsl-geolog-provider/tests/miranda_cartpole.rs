//! Exact-rational CartPole instance for the public Miranda provider.
//!
//! The fixture carries both producer routes: a direct zero certificate on
//! the upright linearization and an equilibrium certificate obtained from
//! a strictly inward unit box after a rational near-eigenvector change of
//! coordinates.  The provider owns the structural walk and face recompute;
//! this test then checks the candidate-B leaf spelling (unsubstituted
//! component on an axis-collapsed box) by an exact corner sweep.

use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use geolog_ground_api::Verdict;
use num_bigint::{BigInt, BigUint};
use qtsl_geolog_provider::miranda::{
    check_battery, decode_battery_kit, MirandaKit, MirandaReadout,
};
use qtsl_geolog_provider::qpoly::QPoly;
use qtsl_geolog_provider::qq::QQ;
use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, qc_v1_container_bytes, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::{Chid, TheoryIndex};
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0xC4; 32];

type Box2 = [(QQ, QQ); 2];

/// A rational as `(numerator, denominator)`.
type Q = (i64, u64);

fn q(n: i64, d: u64) -> QQ {
    QQ::new(BigInt::from(n), BigUint::from(d))
}

fn lref(n: u32) -> Value {
    Value::Ref(ElemRef::Local(n))
}

fn qv(n: i64, d: u64) -> Value {
    Value::Lit(Literal::q(n, d).expect("canonical rational"))
}

struct Body<'a> {
    index: &'a TheoryIndex,
    ops: Vec<Op>,
    next: u32,
}

impl<'a> Body<'a> {
    fn new(index: &'a TheoryIndex) -> Self {
        Self {
            index,
            ops: Vec::new(),
            next: 0,
        }
    }

    fn xref(&self, chid: Chid) -> ElemRef {
        assert_eq!(chid.0, BAKED_QC_V1_REV, "fixture uses the qc closure");
        ElemRef::External {
            dep_index: 0,
            counter: chid.1,
        }
    }

    fn fun(&self, name: &str) -> Chid {
        self.index
            .fun(name)
            .unwrap_or_else(|| panic!("missing `{name}` in baked qc vocabulary"))
            .chid
    }

    fn sort(&self, name: &str) -> Chid {
        self.index
            .sort(name)
            .unwrap_or_else(|| panic!("missing sort `{name}` in baked qc vocabulary"))
    }

    fn fresh(&mut self, sort: &str) -> u32 {
        let n = self.next;
        self.next += 1;
        let s = self.sort(sort);
        self.ops.push(Op::Elta { sort: self.xref(s) });
        n
    }

    fn ctor(&mut self, sort: &str, name: &str, args: Vec<Value>) -> u32 {
        let n = self.fresh(sort);
        let f = self.fun(name);
        self.ops.push(Op::Funa {
            fun: self.xref(f),
            args,
            value: lref(n),
        });
        n
    }

    fn field(&mut self, name: &str, subject: u32, value: Value) {
        let f = self.fun(name);
        self.ops.push(Op::Funa {
            fun: self.xref(f),
            args: vec![lref(subject)],
            value,
        });
    }

    fn interval(&mut self, lo: (i64, u64), hi: (i64, u64)) -> u32 {
        self.ctor(
            "Interval",
            "mkInterval",
            vec![qv(hi.0, hi.1), qv(lo.0, lo.1)],
        )
    }

    fn box_atom(&mut self, axes: &[(Q, Q)]) -> u32 {
        let mut tail = self.ctor("Box", "boxNil", vec![]);
        for &(lo, hi) in axes.iter().rev() {
            let head = self.interval(lo, hi);
            tail = self.ctor("Box", "boxCons", vec![lref(head), lref(tail)]);
        }
        self.ctor("QRegionAtom", "qraBox", vec![lref(tail)])
    }

    fn poly(&mut self, terms: &[((u64, u64), Q)]) -> u32 {
        let mut tail = self.ctor("Poly", "pZero", vec![]);
        for &((e0, e1), (n, d)) in terms.iter().rev() {
            tail = self.ctor(
                "Poly",
                "pTerm",
                vec![qv(n, d), Value::Lit(Literal::shape(&[e0, e1])), lref(tail)],
            );
        }
        tail
    }

    fn polyvec(&mut self, polys: &[u32]) -> u32 {
        let mut tail = self.ctor("PolyVec", "pvNil", vec![]);
        for &head in polys.iter().rev() {
            tail = self.ctor("PolyVec", "pvCons", vec![lref(head), lref(tail)]);
        }
        tail
    }

    fn battery(&mut self, rows: &[(u64, u64, u64, u64)]) -> u32 {
        let mut tail = self.ctor("QMirandaBattery", "qmbNil", vec![]);
        for &(axis, upper, comp, neg) in rows.iter().rev() {
            let proof = self.fresh("QProof");
            tail = self.ctor(
                "QMirandaBattery",
                "qmbCons",
                vec![
                    Value::Lit(Literal::nat(axis)),
                    Value::Lit(Literal::nat(comp)),
                    Value::Lit(Literal::nat(neg)),
                    lref(proof),
                    lref(tail),
                    Value::Lit(Literal::nat(upper)),
                ],
            );
        }
        tail
    }
}

struct Fixture {
    body: Body<'static>,
    direct: [u32; 4],
    inward: [u32; 4],
    direct_node: u32,
    equilibrium_node: u32,
}

fn fixture() -> Fixture {
    let baked = Box::leak(Box::new(
        baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
            .expect("baked qc chain derives"),
    ));
    let mut b = Body::new(&baked.index);
    let empty = b.box_atom(&[]);

    // Route A: x' = (omega, alpha*theta + beta*omega), with the swap
    // pairing.  alpha and beta are derived from l=1/2, g=49/5 and the
    // certified gains K0=-81313/4096, K1=-1169/256.
    let alpha = q(49, 5).add(&q(-81313, 4096)).mul(&q(2, 1));
    let beta = q(-1169, 256).mul(&q(2, 1));
    assert_eq!(alpha, q(-205861, 10240));
    assert_eq!(beta, q(-1169, 128));
    let direct_cell = b.box_atom(&[((-1, 10), (1, 10)), ((-1, 10), (1, 10))]);
    let g0 = b.poly(&[((0, 1), (1, 1))]);
    let g1 = b.poly(&[((1, 0), (-205861, 10240)), ((0, 1), (-1169, 128))]);
    let direct_g = b.polyvec(&[g0, g1]);
    let direct_battery = b.battery(&[(0, 0, 1, 1), (0, 1, 1, 1), (1, 0, 0, 0), (1, 1, 0, 0)]);
    let direct_node = b.fresh("QZeroByMiranda");
    let direct_proof = b.fresh("QProof");
    b.field("QZeroByMiranda/proof", direct_node, lref(direct_proof));
    b.field("QZeroByMiranda/g", direct_node, lref(direct_g));
    b.field("QZeroByMiranda/cell", direct_node, lref(direct_cell));
    b.field("QZeroByMiranda/battery", direct_node, lref(direct_battery));

    // Route B: y' = M y on the unit box.  M is the exact rational
    // near-eigenvector transform of the same closed-loop field.
    let inward_cell = b.box_atom(&[((-1, 1), (1, 1)), ((-1, 1), (1, 1))]);
    let f0 = b.poly(&[((1, 0), (-1639221, 442880)), ((0, 1), (3403, 2214400))]);
    let f1 = b.poly(&[((1, 0), (113, 88576)), ((0, 1), (-2405519, 442880))]);
    let inward_g = b.polyvec(&[f0, f1]);
    let inward_battery = b.battery(&[(0, 0, 0, 1), (0, 1, 0, 1), (1, 0, 1, 1), (1, 1, 1, 1)]);
    let block = b.fresh("QBlockInv");
    let block_proof = b.fresh("QProof");
    let facets = b.ctor("QProofList", "qplNil", vec![]);
    let init_containment = b.fresh("Proof");
    b.field("QBlockInv/proof", block, lref(block_proof));
    b.field("QBlockInv/block", block, lref(inward_cell));
    b.field("QBlockInv/facets", block, lref(facets));
    b.field("QBlockInv/init_containment", block, lref(init_containment));
    let equilibrium_node = b.fresh("QEquilibriumFromInward");
    let equilibrium_proof = b.fresh("QProof");
    b.field(
        "QEquilibriumFromInward/proof",
        equilibrium_node,
        lref(equilibrium_proof),
    );
    b.field("QEquilibriumFromInward/inv", equilibrium_node, lref(block));

    Fixture {
        body: b,
        direct: [direct_battery, direct_cell, direct_g, empty],
        inward: [inward_battery, inward_cell, inward_g, empty],
        direct_node,
        equilibrium_node,
    }
}

fn provider(index: &TheoryIndex) -> QtslGroundProvider {
    let vocab = QtslVocab::build(&[index]);
    assert!(
        vocab.miranda.is_some(),
        "Miranda vocabulary resolves: {:?}",
        vocab.notes
    );
    QtslGroundProvider::new(vec![BAKED_QC_V1_REV], vocab)
}

fn walk(p: &QtslGroundProvider, args: [u32; 4], rows: &CertRows) -> Verdict {
    let local = p
        .local_by_name("qtsl_miranda_battery")
        .expect("public Miranda relation is claimed");
    let cells: Vec<Vec<u8>> = args
        .iter()
        .map(|&e| {
            let mut cell = Vec::new();
            lref(e).encode(&mut cell);
            cell
        })
        .collect();
    let refs: Vec<&[u8]> = cells.iter().map(Vec::as_slice).collect();
    p.filter_rows(local, &refs, rows)
}

fn decoded(
    p: &QtslGroundProvider,
    args: [u32; 4],
    rows: &CertRows,
) -> (MirandaKit, MirandaReadout) {
    let vocab = p.vocab().miranda.as_ref().expect("Miranda vocabulary");
    let vals = args.map(lref);
    let refs: Vec<&Value> = vals.iter().collect();
    let kit =
        decode_battery_kit("qtsl_miranda_battery", vocab, &refs, rows).expect("fixture decodes");
    let readout = check_battery(&kit)
        .expect("within budgets")
        .expect("structurally valid battery");
    (kit, readout)
}

fn corners(b: &Box2) -> Vec<[QQ; 2]> {
    let mut out = Vec::new();
    for x in [&b[0].0, &b[0].1] {
        for y in [&b[1].0, &b[1].1] {
            let point = [x.clone(), y.clone()];
            if !out.contains(&point) {
                out.push(point);
            }
        }
    }
    out
}

fn eval_poly(p: &QPoly, point: &[QQ; 2]) -> QQ {
    let mut total = QQ::zero();
    for (mono, coeff) in &p.0 {
        let mut term = coeff.clone();
        for (var, exp) in mono {
            for _ in 0..*exp {
                term = term.mul(&point[*var as usize]);
            }
        }
        total = total.add(&term);
    }
    total
}

#[derive(Clone)]
struct Leaf {
    subject: QPoly,
    region: Box2,
    ge_zero: bool,
}

fn candidate_b_leaves(kit: &MirandaKit) -> Vec<Leaf> {
    kit.rows
        .iter()
        .map(|r| {
            let mut region: Box2 = kit
                .cell
                .clone()
                .try_into()
                .expect("two-dimensional fixture");
            let bound = if r.upper == 1 {
                region[r.axis as usize].1.clone()
            } else {
                region[r.axis as usize].0.clone()
            };
            region[r.axis as usize] = (bound.clone(), bound);
            let base_ge = r.upper == 1;
            Leaf {
                subject: kit.g[r.comp as usize].clone(),
                region,
                ge_zero: if r.neg == 1 { !base_ge } else { base_ge },
            }
        })
        .collect()
}

fn leaf_margin(leaf: &Leaf) -> Result<QQ, QQ> {
    let values: Vec<QQ> = corners(&leaf.region)
        .iter()
        .map(|p| eval_poly(&leaf.subject, p))
        .collect();
    if leaf.ge_zero {
        let least = values
            .into_iter()
            .min_by(QQ::cmp_qq)
            .expect("nonempty corners");
        if least.is_nonneg() {
            Ok(least)
        } else {
            Err(least.neg())
        }
    } else {
        let greatest = values
            .into_iter()
            .max_by(QQ::cmp_qq)
            .expect("nonempty corners");
        if greatest.cmp_qq(&QQ::zero()).is_le() {
            Ok(greatest.neg())
        } else {
            Err(greatest)
        }
    }
}

fn candidate_b_tie(kit: &MirandaKit, leaves: &[Leaf]) -> Result<(), &'static str> {
    if leaves.len() != kit.rows.len() {
        return Err("leaf count");
    }
    for (row, leaf) in kit.rows.iter().zip(leaves) {
        if leaf.subject != kit.g[row.comp as usize] {
            return Err("subject");
        }
        let mut region: Box2 = kit.cell.clone().try_into().map_err(|_| "dimension")?;
        let bound = if row.upper == 1 {
            region[row.axis as usize].1.clone()
        } else {
            region[row.axis as usize].0.clone()
        };
        region[row.axis as usize] = (bound.clone(), bound);
        if leaf.region != region {
            return Err("region");
        }
        let base_ge = row.upper == 1;
        let expected_ge = if row.neg == 1 { !base_ge } else { base_ge };
        if leaf.ge_zero != expected_ge {
            return Err("sign");
        }
    }
    Ok(())
}

fn assert_leaf_margins(leaves: &[Leaf], expected: &[QQ]) {
    let got: Vec<QQ> = leaves
        .iter()
        .map(|leaf| leaf_margin(leaf).expect("leaf holds"))
        .collect();
    assert_eq!(got, expected);
}

#[test]
fn cartpole_routes_walk_and_candidate_b_leaves_accept_exactly() {
    let fx = fixture();
    let rows = CertRows::from_ops(&fx.body.ops, OWN, &[BAKED_QC_V1_REV]);
    let p = provider(fx.body.index);

    assert_ne!(fx.direct_node, fx.equilibrium_node);
    assert_eq!(walk(&p, fx.direct, &rows), Verdict::Holds);
    assert_eq!(walk(&p, fx.inward, &rows), Verdict::Holds);

    let (direct, direct_readout) = decoded(&p, fx.direct, &rows);
    let (inward, inward_readout) = decoded(&p, fx.inward, &rows);
    assert_eq!(direct_readout.sequents.len(), 4);
    assert_eq!(inward_readout.sequents.len(), 4);

    let direct_leaves = candidate_b_leaves(&direct);
    let inward_leaves = candidate_b_leaves(&inward);
    assert_eq!(candidate_b_tie(&direct, &direct_leaves), Ok(()));
    assert_eq!(candidate_b_tie(&inward, &inward_leaves), Ok(()));

    assert_leaf_margins(
        &direct_leaves,
        &[q(112341, 102400), q(112341, 102400), q(1, 10), q(1, 10)],
    );
    assert_leaf_margins(
        &inward_leaves,
        &[
            q(4096351, 1107200),
            q(4096351, 1107200),
            q(1202477, 221440),
            q(1202477, 221440),
        ],
    );
}

#[test]
fn candidate_b_tie_mutants_refuse_at_their_intended_layers() {
    let fx = fixture();
    let rows = CertRows::from_ops(&fx.body.ops, OWN, &[BAKED_QC_V1_REV]);
    let p = provider(fx.body.index);
    let (kit, _) = decoded(&p, fx.inward, &rows);
    let leaves = candidate_b_leaves(&kit);

    // Candidate-A bytes cannot be cross-fed into the candidate-B tie:
    // both the subject and the full-box region differ.
    let mut cross_feed = leaves.clone();
    cross_feed[0].subject = kit.g[0].substitute_var(0, &q(-1, 1)).neg();
    cross_feed[0].region = kit.cell.clone().try_into().unwrap();
    assert_ne!(cross_feed[0].subject, leaves[0].subject);
    assert_ne!(cross_feed[0].region, leaves[0].region);
    assert_eq!(candidate_b_tie(&kit, &cross_feed), Err("subject"));

    // The converse cross-feed is represented by a candidate-B leaf read
    // under candidate A's full-box/substituted-subject contract.
    let a_subject = kit.g[0].substitute_var(0, &q(-1, 1)).neg();
    assert_ne!(leaves[0].subject, a_subject);
    let full_box: Box2 = kit.cell.clone().try_into().unwrap();
    assert_ne!(leaves[0].region, full_box);

    // Widening the thin leaf to the full box fails the geometry tie and
    // is materially false at an exact corner.
    let mut widened = leaves[0].clone();
    widened.region = kit.cell.clone().try_into().unwrap();
    assert_ne!(widened.region, leaves[0].region);
    widened.ge_zero = true;
    let mut widened_fixture = leaves.clone();
    widened_fixture[0] = widened.clone();
    assert_eq!(candidate_b_tie(&kit, &widened_fixture), Err("region"));
    // The tie-decision receipt uses the Euler map flavor, so its derived
    // subject is exactly tau=1/50 times this drift component.
    let widened_map = Leaf {
        subject: widened.subject.scale(&q(1, 50)),
        ..widened
    };
    assert_eq!(leaf_margin(&widened_map), Err(q(11849, 160000)));

    // Leaving negation unfolded flips the metadata-resolved claim.
    let mut sign = leaves[0].clone();
    sign.ge_zero = !sign.ge_zero;
    assert_ne!(sign.ge_zero, leaves[0].ge_zero);
    let mut sign_fixture = leaves.clone();
    sign_fixture[0] = sign;
    assert_eq!(candidate_b_tie(&kit, &sign_fixture), Err("sign"));
}

#[test]
fn transported_delta_eight_walks_then_fails_at_the_leaf() {
    let mut fx = fixture();
    // Add the transported offset (800/173, -800/173) to the two y-field
    // components by replacing the PolyVec argument with exact new rows.
    let f0 = fx.body.poly(&[
        ((0, 0), (800, 173)),
        ((1, 0), (-1639221, 442880)),
        ((0, 1), (3403, 2214400)),
    ]);
    let f1 = fx.body.poly(&[
        ((0, 0), (-800, 173)),
        ((1, 0), (113, 88576)),
        ((0, 1), (-2405519, 442880)),
    ]);
    fx.inward[2] = fx.body.polyvec(&[f0, f1]);

    let rows = CertRows::from_ops(&fx.body.ops, OWN, &[BAKED_QC_V1_REV]);
    let p = provider(fx.body.index);
    assert_eq!(walk(&p, fx.inward, &rows), Verdict::Holds);

    let (kit, readout) = decoded(&p, fx.inward, &rows);
    assert_eq!(
        readout.sequents.len(),
        4,
        "the structural face walk completes"
    );
    let leaves = candidate_b_leaves(&kit);
    assert_eq!(leaf_margin(&leaves[1]), Err(q(1023649, 1107200)));
}
