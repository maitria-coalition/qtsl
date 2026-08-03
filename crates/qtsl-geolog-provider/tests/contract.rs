//! The primitive-box semiring-cell family exercised end to end
//! through provider dispatch: `qtsl_contract_param`
//! (conjugation-parameter conformance, exactly as
//! `qtsl_hplate_param_wire`) and `qtsl_contract_cell` v1 (hagSum
//! decides TRUE; conjugated kinds loud-defer with the case named;
//! idempotent kinds decide FALSE — no φ-route exists structurally).
//!
//! Verdict-per-kind goldens, the parameter mutants at named gates
//! (integrality, the p ≥ 1 floor, the even-p range refusal), the
//! loud-deferral witnesses (message content asserted — a deferral
//! that loses its named successor is a regression), the
//! violations-register probe (decided-false branches carry
//! adjudication words through the F-4 seam), and refusal witnesses.
//!
//! The test-side row emitter shares no code with the evaluators.

mod common;

use common::{provider, stack, STACK};
use geolog_envelope::body::Op;
use geolog_envelope::{ElemRef, Literal, Value};
use qtsl_geolog_provider::rowctx::CertRows;
use qtsl_geolog_provider::theory::Chid;
use qtsl_geolog_provider::{QtslGroundProvider, QtslVocab};

const OWN: [u8; 32] = [0xC5; 32];

fn s_fun(name: &str) -> Chid {
    stack()
        .fun(name)
        .unwrap_or_else(|| panic!("stack fun `{name}`"))
        .chid
}

fn lref(e: u32) -> Value {
    Value::Ref(ElemRef::Local(e))
}

fn qv(num: i64, den: u64) -> Value {
    Value::Lit(Literal::q(num, den).expect("canonical q"))
}

struct Body {
    ops: Vec<Op>,
    next: u32,
    deps: Vec<[u8; 32]>,
}

impl Body {
    fn new() -> Body {
        Body {
            ops: Vec::new(),
            next: 0,
            deps: vec![STACK],
        }
    }

    fn xref(&self, c: Chid) -> ElemRef {
        let dep_index = self
            .deps
            .iter()
            .position(|d| *d == c.0)
            .expect("chid homed in a dep") as u32;
        ElemRef::External {
            dep_index,
            counter: c.1,
        }
    }

    fn fresh(&mut self) -> u32 {
        let e = self.next;
        self.next += 1;
        e
    }

    fn ctor(&mut self, fun: &str, args: Vec<Value>) -> u32 {
        let e = self.fresh();
        self.ops.push(Op::Funa {
            fun: self.xref(s_fun(fun)),
            args,
            value: lref(e),
        });
        e
    }

    /// A `contract_semiring {app, kind, param}` cell row (wire field
    /// order is bytewise: app, kind, param).
    fn cell(&mut self, app: u32, kind: u32, param: (i64, u64)) {
        self.ops.push(Op::Rela {
            rel: self.xref(s_fun("contract_semiring")),
            args: vec![lref(app), lref(kind), qv(param.0, param.1)],
        });
    }

    /// An app with one cell of the given kind constructor and param.
    fn celled_app(&mut self, kind_ctor: &str, param: (i64, u64)) -> u32 {
        let app = self.fresh();
        let kind = self.ctor(kind_ctor, vec![]);
        self.cell(app, kind, param);
        app
    }

    fn rows(&self) -> CertRows {
        CertRows::from_ops(&self.ops, OWN, &self.deps)
    }
}

fn ev_app(name: &str, app: u32, b: &Body) -> Result<bool, String> {
    let args = [lref(app)];
    let refs: Vec<&Value> = args.iter().collect();
    common::ev(name, &refs, &b.rows())
}

#[test]
fn both_claimed() {
    for name in ["qtsl_contract_param", "qtsl_contract_cell"] {
        assert!(provider().local_by_name(name).is_some(), "`{name}` claimed");
    }
}

/// The fields-vs-theory citation gate: `{app: PrimApp}` for both.
#[test]
fn claim_fields_match_the_declared_signatures() {
    use geolog_ground_api::GroundProvider;
    for name in ["qtsl_contract_param", "qtsl_contract_cell"] {
        let rel = provider()
            .relations()
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("`{name}` among the claimed expectations"));
        let got: Vec<(&str, &str)> = rel.fields.to_vec();
        assert_eq!(got, vec![("app", "PrimApp")], "`{name}` claim fields");
    }
}

// ---------------------------------------------------------------------
// Verdict-per-kind goldens.
// ---------------------------------------------------------------------

/// No cell rows: the theory's back-compat is default-absent — no
/// conformance content to violate, both relations decide TRUE.
#[test]
fn no_cell_rows_hold() {
    let mut b = Body::new();
    let app = b.fresh();
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(true));
    assert_eq!(ev_app("qtsl_contract_cell", app, &b), Ok(true));
}

/// hagSum: φ = id, the default made formal — both hold.
#[test]
fn sum_cell_holds_both() {
    let mut b = Body::new();
    let app = b.celled_app("hagSum", (0, 1));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(true));
    assert_eq!(ev_app("qtsl_contract_cell", app, &b), Ok(true));
}

/// hagConjPow at odd integral p ≥ 1: the parameter conforms
/// (order-preserving on all of ℚ).
#[test]
fn pow_odd_param_holds() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (3, 1));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(true));
}

/// p = 1 (the floor itself, odd): conforms.
#[test]
fn pow_p_one_param_holds() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (1, 1));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(true));
}

/// hagConjPow under the cell relation: loud deferral naming its
/// successor (the semiring-generic evaluator) — never a silent pass,
/// never a decided verdict.
#[test]
fn pow_cell_defers_loudly() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (3, 1));
    let err = ev_app("qtsl_contract_cell", app, &b).unwrap_err();
    assert!(err.contains("semiring-generic"), "{err}");
    assert!(err.contains("T-TRANSFER"), "{err}");
}

/// hagConjExp: the parameter relation defers on the enclosure
/// register; the cell relation defers on the certified-enclosure
/// boundary design.
#[test]
fn exp_defers_loudly_both() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjExp", (1, 2));
    let perr = ev_app("qtsl_contract_param", app, &b).unwrap_err();
    assert!(perr.contains("enclosure register"), "{perr}");
    let cerr = ev_app("qtsl_contract_cell", app, &b).unwrap_err();
    assert!(cerr.contains("certified-enclosure"), "{cerr}");
}

/// hagMax / hagMin under the cell relation: decided FALSE (no
/// φ-route exists structurally — a stable verdict, not a deferral);
/// under the parameter relation: TRUE (no conjugation parameter to
/// conform).
#[test]
fn idempotent_kinds_decide_false_on_cell() {
    for k in ["hagMax", "hagMin"] {
        let mut b = Body::new();
        let app = b.celled_app(k, (0, 1));
        assert_eq!(ev_app("qtsl_contract_cell", app, &b), Ok(false), "{k}");
        assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(true), "{k}");
    }
}

/// A kind element produced by a constructor OUTSIDE the five: closed
/// by construction — the cell relation decides FALSE; the parameter
/// relation has no conjugation content (TRUE).
#[test]
fn unknown_kind_ctor_decides_false_on_cell() {
    let mut b = Body::new();
    let app = b.fresh();
    // Type-wrong at row grain on purpose: any non-HAggKind ctor.
    let bogus = b.ctor("PReLU", vec![]);
    b.cell(app, bogus, (1, 1));
    assert_eq!(ev_app("qtsl_contract_cell", app, &b), Ok(false));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(true));
}

// ---------------------------------------------------------------------
// Parameter mutants at named gates.
// ---------------------------------------------------------------------

/// Non-integral p — the integrality gate.
#[test]
fn mutant_non_integral_p_decides_false() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (5, 2));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(false));
}

/// p = 0 — the p ≥ 1 floor (integral, below).
#[test]
fn mutant_p_zero_decides_false() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (0, 1));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(false));
}

/// p = −3 — the floor again, negative flavor (odd, so the parity arm
/// cannot mask the floor).
#[test]
fn mutant_negative_p_decides_false() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (-3, 1));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(false));
}

/// Even p ≥ 1: the order-preservation domain demands a certified
/// nonnegative operand range, which has no relational home at the
/// current staging — REFUSES (never a silent pass, never a decided
/// false: the state is undecidable, not wrong).
#[test]
fn even_p_refuses_on_the_range_home() {
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (2, 1));
    let err = ev_app("qtsl_contract_param", app, &b).unwrap_err();
    assert!(err.contains("nonnegative"), "{err}");
    assert!(err.contains("operand range"), "{err}");
}

/// Two cells, the second nonconforming: the walk reaches every row
/// (a sum cell cannot shadow a broken pow cell).
#[test]
fn second_row_violation_decides_false() {
    let mut b = Body::new();
    let app = b.fresh();
    let sum = b.ctor("hagSum", vec![]);
    b.cell(app, sum, (0, 1));
    let pow = b.ctor("hagConjPow", vec![]);
    b.cell(app, pow, (1, 2));
    assert_eq!(ev_app("qtsl_contract_param", app, &b), Ok(false));
}

// ---------------------------------------------------------------------
// The violations register (design memo F-4, generalized past the
// store seam): decided-false branches carry their adjudication words.
// ---------------------------------------------------------------------

/// A FRESH provider (never the shared fixture — the register is a
/// drain, and parallel tests would race it): the integrality
/// decided-false banks `"qtsl_contract_param: …"` in the register.
#[test]
fn decided_false_banks_the_named_violation() {
    let vocab = QtslVocab::build(&common::sweep_indices());
    let p = QtslGroundProvider::new(vec![common::REV], vocab);
    let mut b = Body::new();
    let app = b.celled_app("hagConjPow", (5, 2));
    let local = p
        .local_by_name("qtsl_contract_param")
        .expect("claimed on the synthetic stack");
    let arg = lref(app);
    let mut cell_bytes = Vec::new();
    arg.encode(&mut cell_bytes);
    let verdict = p.filter_rows(local, &[cell_bytes.as_slice()], &b.rows());
    assert!(matches!(verdict, geolog_ground_api::Verdict::Fails));
    let violations = p.take_violations();
    assert_eq!(violations.len(), 1, "{violations:?}");
    assert!(
        violations[0].starts_with("qtsl_contract_param:"),
        "{violations:?}"
    );
    assert!(violations[0].contains("not integral"), "{violations:?}");
    // Drained: a second take is empty.
    assert!(p.take_violations().is_empty());
}

// ---------------------------------------------------------------------
// Refusal witnesses.
// ---------------------------------------------------------------------

/// A kind element with no constructor row: structure undecidable.
#[test]
fn unresolvable_kind_refuses() {
    let mut b = Body::new();
    let app = b.fresh();
    let ghost = b.fresh();
    b.cell(app, ghost, (1, 1));
    let err = ev_app("qtsl_contract_cell", app, &b).unwrap_err();
    assert!(err.contains("no constructor row"), "{err}");
}

/// An external app element: single-body context.
#[test]
fn external_app_refuses() {
    let b = Body::new();
    let ext = Value::Ref(ElemRef::External {
        dep_index: 0,
        counter: 970,
    });
    let args = [ext];
    let refs: Vec<&Value> = args.iter().collect();
    let err = common::ev("qtsl_contract_param", &refs, &b.rows()).unwrap_err();
    assert!(err.contains("external"), "{err}");
}
