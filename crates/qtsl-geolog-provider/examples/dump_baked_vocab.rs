//! Dump the FULL derived vocabulary of both baked closures (qc, dc) as
//! `kind dep counter name [meta]` rows — the generation instrument for
//! downstream pin tables (first consumer: the Lean-side
//! `decodeQtslPresentation` fragment pins).
//!
//! The derivation is `reprovocab::baked`'s own (`load_revision` →
//! `revision_view` → `DepView` → `TheoryIndex`): pins are the four
//! chids, everything else is derived from the embedded chain
//! containers' bytes. This example only PRINTS what the checker
//! already derives — it asserts nothing new.
//!
//! Output row grammar (space-separated):
//!   `sort <dep> <counter> <name>`
//!   `fun  <dep> <counter> <name> <class> [<codomain>]`
//! where `<dep>` is 0 = qc, 1 = dc (the `baked_v1_pins.txt` fixture's
//! own convention), and `<class>` is one of `field` (unary domain,
//! valued), `ctor` (record/nullary domain, valued), `rel` (relational,
//! not side-condition), `sidecond` (relational side-condition).

use qtsl_geolog_provider::reprovocab::baked::{
    baked_vocab_from_container, dc_v1_container_bytes, qc_v1_container_bytes, BakedVocab,
    BAKED_DC_V1_REV, BAKED_QC_V1_REV,
};
use qtsl_geolog_provider::theory::DomainSig;

fn dump(dep: usize, v: &BakedVocab) {
    let mut sorts: Vec<(u32, &str)> = v
        .index
        .sorts_by_chid
        .iter()
        .filter(|((commit, _), _)| *commit == v.revision)
        .map(|((_, counter), name)| (*counter, name.as_str()))
        .collect();
    sorts.sort();
    for (counter, name) in sorts {
        println!("sort {dep} {counter} {name}");
    }
    let mut funs: Vec<(u32, String)> = v
        .index
        .funs
        .iter()
        .filter(|f| f.chid.0 == v.revision)
        .map(|f| {
            let class = if f.relational {
                if f.side_condition {
                    "sidecond"
                } else {
                    "rel"
                }
            } else {
                match f.domain {
                    DomainSig::Unary(_) => "field",
                    _ => "ctor",
                }
            };
            let cod = match &f.codomain {
                Some(k) => format!(" {k:?}"),
                None => String::new(),
            };
            (
                f.chid.1,
                format!("fun {dep} {} {} {class}{cod}", f.chid.1, f.name),
            )
        })
        .collect();
    funs.sort();
    for (_, line) in funs {
        println!("{line}");
    }
}

fn main() {
    let qc = baked_vocab_from_container(qc_v1_container_bytes(), BAKED_QC_V1_REV)
        .expect("qc chain derivation");
    let dc = baked_vocab_from_container(dc_v1_container_bytes(), BAKED_DC_V1_REV)
        .expect("dc chain derivation");
    println!(
        "# baked v1 full vocabulary dump — qc rev {} / dc rev {}",
        qtsl_geolog_provider::container::hex32(&BAKED_QC_V1_REV),
        qtsl_geolog_provider::container::hex32(&BAKED_DC_V1_REV)
    );
    println!(
        "# qc stats: {} sorts / {} funs; dc stats: {} sorts / {} funs",
        qc.stats.sorts, qc.stats.funs, dc.stats.sorts, dc.stats.funs
    );
    dump(0, &qc);
    dump(1, &dc);
}
