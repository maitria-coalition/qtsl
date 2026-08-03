//! qtsl-rules — diff-typeset the Bernstein Logic derivation rules.
//!
//! Two-column Steele-metanotation diff of the paper's original rules (left,
//! the April 2026 paper, TeX verbatim) against the Lean realization
//! (right), one deduction rule per row, red = left-only, blue = right-only,
//! soundness marks on the outer margin — DERIVED live from the Lean tree
//! at every render (src/marks.rs), never hand-maintained.
//!
//! Verbs (rg-style: one obvious verb, rich defaults, works from anywhere):
//!   qtsl-rules [render] [--rules F] [--out D] [--lean D] [--no-compile] [--no-verify]
//!   qtsl-rules check    [--rules F] [--lean D]     # marks + round-trip, no TeX

use qtsl_metanotation::doc::{
    build_document, check_rule_enum, ruletag_enum, validate_tiers, RulesFile,
};
use qtsl_metanotation::marks;
use std::path::PathBuf;
use std::process::Command;

const NAMESPACE: &str = "PPLC";
/// root modules of the two Lean packages the marks probe can reach:
/// `lemmas` resolve through the main package, `aux_lemmas` (fully
/// qualified) through the auxiliary one.
const MAIN_IMPORT: &str = "Qtsl";
const AUX_IMPORT: &str = "QtslAux";

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn fail(msg: &str) -> ! {
    eprintln!("qtsl-rules: {msg}");
    std::process::exit(1);
}

fn main() {
    let mut rules_path = manifest_dir().join("../BL-rules.toml");
    let mut out_dir = manifest_dir().join("out");
    // The reference Qtsl Lean package is not yet imported into this
    // repository; soundness-mark derivation needs --lean pointing at a checkout.
    let mut lean_dir = manifest_dir().join("../lean");
    let mut lean_aux_dir = manifest_dir().join("../../lean");
    let mut compile = true;
    let mut verify = true;
    let mut verb = "render".to_string();

    let mut args = std::env::args().skip(1).peekable();
    if let Some(first) = args.peek() {
        if !first.starts_with('-') {
            verb = args.next().unwrap();
        }
    }
    while let Some(a) = args.next() {
        match a.as_str() {
            "--rules" => rules_path = PathBuf::from(args.next().expect("--rules <path>")),
            "--out" => out_dir = PathBuf::from(args.next().expect("--out <dir>")),
            "--lean" => lean_dir = PathBuf::from(args.next().expect("--lean <dir>")),
            "--qtsl-aux" => lean_aux_dir = PathBuf::from(args.next().expect("--qtsl-aux <dir>")),
            "--no-compile" => compile = false,
            "--no-verify" => verify = false,
            "--help" | "-h" => {
                eprintln!(
                    "qtsl-rules [render|check] [--rules F] [--out D] [--lean D] [--qtsl-aux D] \
                     [--no-compile] [--no-verify]"
                );
                return;
            }
            other => fail(&format!("unknown arg: {other}")),
        }
    }
    if !matches!(verb.as_str(), "render" | "check") {
        fail(&format!("unknown verb: {verb} (render | check)"));
    }

    let raw = std::fs::read_to_string(&rules_path)
        .unwrap_or_else(|e| fail(&format!("cannot read {}: {e}", rules_path.display())));
    let rf: RulesFile =
        toml::from_str(&raw).unwrap_or_else(|e| fail(&format!("rules parse error: {e}")));
    eprintln!(
        "{} rules loaded from {}",
        rf.rules.len(),
        rules_path.display()
    );
    validate_tiers(&rf).unwrap_or_else(|e| fail(&e));

    // ---- extraction round-trip: rows vs the Lean RuleTag enum ----
    if rf.meta.rule_enum_check {
        let cat = lean_dir.join("Qtsl/Core/Catalogue.lean");
        let src = std::fs::read_to_string(&cat)
            .unwrap_or_else(|e| fail(&format!("cannot read {}: {e}", cat.display())));
        let tags = ruletag_enum(&src).unwrap_or_else(|e| fail(&e));
        // tagged rows on declared sibling pages count toward the pairing
        // (rule_enum_also, doc.rs) — retained for pages that declare it;
        // the base page carries the composition rows itself since the
        // 2026-08-02 fold, so today the list is typically empty.
        let base = rules_path
            .parent()
            .unwrap_or_else(|| std::path::Path::new("."));
        let mut also_tags: Vec<String> = Vec::new();
        for rel in &rf.meta.rule_enum_also {
            let p = base.join(rel);
            let raw2 = std::fs::read_to_string(&p).unwrap_or_else(|e| {
                fail(&format!("rule_enum_also: cannot read {}: {e}", p.display()))
            });
            let rf2: RulesFile = toml::from_str(&raw2).unwrap_or_else(|e| {
                fail(&format!("rule_enum_also {}: parse error: {e}", p.display()))
            });
            also_tags.extend(
                rf2.rules
                    .iter()
                    .filter(|r| !r.tag.is_empty())
                    .map(|r| r.tag.clone()),
            );
        }
        check_rule_enum(&rf, &also_tags, &tags).unwrap_or_else(|e| fail(&e));
        eprintln!(
            "rule-enum round-trip: {} tags, all paired ({} via rule_enum_also)",
            tags.len(),
            also_tags.len()
        );
    }

    // ---- live marks derivation (per package: main lemmas + aux lemmas) ----
    let mut all_lemmas: Vec<String> = Vec::new();
    let mut all_aux_lemmas: Vec<String> = Vec::new();
    for r in &rf.rules {
        for l in &r.lemmas {
            if !all_lemmas.contains(l) {
                all_lemmas.push(l.clone());
            }
        }
        for l in &r.aux_lemmas {
            if !all_aux_lemmas.contains(l) {
                all_aux_lemmas.push(l.clone());
            }
        }
    }
    let derivation = if verify {
        let d = marks::derive(&lean_dir, MAIN_IMPORT, NAMESPACE, &all_lemmas, &out_dir)
            .unwrap_or_else(|e| fail(&e));
        let d = if all_aux_lemmas.is_empty() {
            d
        } else {
            let aux = marks::derive(
                &lean_aux_dir,
                AUX_IMPORT,
                NAMESPACE,
                &all_aux_lemmas,
                &out_dir,
            )
            .unwrap_or_else(|e| fail(&e));
            marks::merge(d, aux)
        };
        std::fs::create_dir_all(&out_dir).expect("mkdir out");
        let report_path = out_dir.join("marks-derivation.txt");
        std::fs::write(&report_path, &d.report).expect("write derivation report");
        eprintln!("marks: derivation recorded at {}", report_path.display());
        Some(d)
    } else {
        eprintln!("marks: --no-verify — declared mode, marks NOT re-derived this run");
        None
    };

    if verb == "check" {
        // compose everything (validates lemma table coverage) but emit nothing
        let table = derivation.as_ref().map(|d| &d.table);
        for r in &rf.rules {
            qtsl_metanotation::doc::compose_marks(r, table).unwrap_or_else(|e| fail(&e));
        }
        eprintln!("check: green");
        return;
    }

    // ---- render ----
    let stamp = match &derivation {
        Some(d) => d.stamp.clone(),
        None => "\\textcolor{NoteGray}{\\footnotesize Marks NOT re-derived this run \
                 (--no-verify): check marks reflect the last derivation, not this tree.}"
            .to_string(),
    };
    let tex = build_document(&rf, derivation.as_ref().map(|d| &d.table), &stamp)
        .unwrap_or_else(|e| fail(&e));

    std::fs::create_dir_all(&out_dir).expect("mkdir out");
    let base = rf
        .meta
        .basename
        .clone()
        .unwrap_or_else(|| "BL-rules-diff".into());
    let tex_path = out_dir.join(format!("{base}.tex"));
    std::fs::write(&tex_path, tex).expect("write tex");
    eprintln!("wrote {}", tex_path.display());

    if compile {
        let status = Command::new("latexmk")
            .args(["-lualatex", "-interaction=nonstopmode", "-halt-on-error"])
            .arg(format!("{base}.tex"))
            .current_dir(&out_dir)
            .status()
            .expect("latexmk not found");
        if !status.success() {
            fail(&format!(
                "latexmk failed — see {}/{base}.log",
                out_dir.display()
            ));
        }
        eprintln!("compiled {}", out_dir.join(format!("{base}.pdf")).display());

        // print variant: some print pipelines refuse landscape-dimension
        // pages (portrait A4 holders), so re-impose rotated onto
        // portrait. print with short-edge/tumble duplex (it keeps
        // rotated-landscape backs upright).
        let status = Command::new("pdfjam")
            .args([
                "--quiet",
                "--angle",
                "90",
                "--paper",
                "a4paper",
                "--outfile",
            ])
            .arg(format!("{base}-print.pdf"))
            .arg(format!("{base}.pdf"))
            .current_dir(&out_dir)
            .status();
        match status {
            Ok(s) if s.success() => eprintln!(
                "print variant {} (print with short-edge duplex)",
                out_dir.join(format!("{base}-print.pdf")).display()
            ),
            _ => eprintln!("pdfjam unavailable/failed — print variant skipped"),
        }
    }
}
