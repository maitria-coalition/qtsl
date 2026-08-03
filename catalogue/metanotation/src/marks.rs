//! Live marks derivation: the check marks on the rules page are re-derived
//! from the Lean tree at every render (2026-07-17) — the
//! tool asks the kernel, not a hand-maintained table.
//!
//! Mechanism: `lake build` (incremental; a no-op seconds when the tree is
//! current), then one scratch file of `#print axioms PPLC.<lemma>` lines
//! through `lake env lean`, parsed into per-lemma axiom closures.
//! Classification:
//!   Green  — closure ⊆ {propext, Classical.choice, Quot.sound}
//!            (the kernel-certified state; empty closure also qualifies)
//!   Sorry  — closure contains a sorryAx (proof in flight; demotes the mark)
//!   anything else — hard error: an unexpected axiom in this development is
//!            a discipline violation, not a rendering choice.
//! A missing declaration is a hard error too (a phantom citation — the
//! defect class that motivated derivation: `sound_farkas_singleton` was
//! renamed and the printed page kept citing it).

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

#[derive(Debug, Clone)]
pub enum Closure {
    Green(Vec<String>),
    Sorry(Vec<String>),
}

pub type LemmaTable = HashMap<String, Closure>;

pub struct Derivation {
    pub table: LemmaTable,
    /// human-auditable record: one line per lemma + environment stamps.
    pub report: String,
    /// one-line TeX stamp for the colophon.
    pub stamp: String,
}

const ALLOWED: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

fn run(cmd: &mut Command, what: &str) -> Result<std::process::Output, String> {
    let out = cmd
        .output()
        .map_err(|e| format!("{what}: cannot launch: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "{what} failed ({}):\n{}\n{}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(out)
}

/// Parse `#print axioms` output. Handles both phrasings:
///   'X' depends on axioms: [a, b, c]
///   'X' does not depend on any axioms
/// Output may wrap across lines inside the bracket list; the whole stream
/// is scanned as one string.
fn parse_axioms(out: &str) -> HashMap<String, Vec<String>> {
    let mut map = HashMap::new();
    let flat = out.replace('\n', " ");
    let mut rest = flat.as_str();
    while let Some(q0) = rest.find('\'') {
        let after = &rest[q0 + 1..];
        let Some(q1) = after.find('\'') else { break };
        let name = &after[..q1];
        let tail = &after[q1 + 1..];
        if let Some(t) = tail.strip_prefix(" does not depend on any axioms") {
            map.insert(name.to_string(), Vec::new());
            rest = t;
        } else if let Some(t) = tail.strip_prefix(" depends on axioms: [") {
            let Some(close) = t.find(']') else { break };
            let axioms: Vec<String> = t[..close]
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            map.insert(name.to_string(), axioms);
            rest = &t[close + 1..];
        } else {
            rest = tail;
        }
    }
    map
}

fn classify(name: &str, axioms: &[String]) -> Result<Closure, String> {
    if axioms.iter().any(|a| a.starts_with("sorryAx")) {
        return Ok(Closure::Sorry(axioms.to_vec()));
    }
    let unexpected: Vec<&String> = axioms
        .iter()
        .filter(|a| !ALLOWED.contains(&a.as_str()))
        .collect();
    if unexpected.is_empty() {
        Ok(Closure::Green(axioms.to_vec()))
    } else {
        Err(format!(
            "lemma {name}: UNEXPECTED axioms {unexpected:?} — closure must stay within \
             {ALLOWED:?}; refusing to render a check mark over an unaudited axiom"
        ))
    }
}

fn shell_line(cmd: &str, args: &[&str]) -> String {
    match Command::new(cmd).args(args).output() {
        Ok(o) if o.status.success() => String::from_utf8_lossy(&o.stdout).trim().to_string(),
        _ => "unknown".to_string(),
    }
}

/// Derive the closure table for `lemmas` (bare names; resolved in
/// `namespace`) against the Lean package at `lean_dir`, probing through
/// `import_root` (the package's root module — "Qtsl" for the
/// main package, "QtslAux" for the auxiliary one).
pub fn derive(
    lean_dir: &Path,
    import_root: &str,
    namespace: &str,
    lemmas: &[String],
    scratch: &Path,
) -> Result<Derivation, String> {
    if lemmas.is_empty() {
        return Ok(Derivation {
            table: HashMap::new(),
            report: "no lemmas cited; nothing derived\n".into(),
            stamp: String::new(),
        });
    }
    eprintln!("marks: lake build (incremental, {import_root}) …");
    run(
        Command::new("lake").arg("build").current_dir(lean_dir),
        "lake build",
    )?;

    let mut probe = String::new();
    probe.push_str(&format!("import {import_root}\n"));
    for l in lemmas {
        let qualified = if l.contains('.') {
            l.clone()
        } else {
            format!("{namespace}.{l}")
        };
        probe.push_str(&format!("#print axioms {qualified}\n"));
    }
    std::fs::create_dir_all(scratch).map_err(|e| e.to_string())?;
    let probe_path = scratch.join(format!("axioms-probe-{import_root}.lean"));
    std::fs::write(&probe_path, &probe).map_err(|e| e.to_string())?;

    eprintln!("marks: #print axioms on {} lemmas …", lemmas.len());
    let out = run(
        Command::new("lake")
            .args(["env", "lean"])
            .arg(&probe_path)
            .current_dir(lean_dir),
        "lake env lean (axioms probe)",
    )?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let parsed = parse_axioms(&stdout);

    let mut table = HashMap::new();
    let mut report = String::new();
    let toolchain = std::fs::read_to_string(lean_dir.join("lean-toolchain"))
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|_| "unknown".into());
    let rev = shell_line(
        "git",
        &[
            "-C",
            &lean_dir.to_string_lossy(),
            "rev-parse",
            "--short",
            "HEAD",
        ],
    );
    let dirty = !shell_line(
        "git",
        &[
            "-C",
            &lean_dir.to_string_lossy(),
            "status",
            "--porcelain",
            ".",
        ],
    )
    .is_empty();
    let when = shell_line("date", &["-u", "+%Y-%m-%dT%H:%M:%SZ"]);
    report.push_str(&format!(
        "marks derivation — {when}\ntoolchain {toolchain} · tree {rev}{} · namespace {namespace}\n\n",
        if dirty { "+dirty" } else { "" }
    ));
    let mut n_green = 0usize;
    let mut n_sorry = 0usize;
    for l in lemmas {
        let qualified = if l.contains('.') {
            l.clone()
        } else {
            format!("{namespace}.{l}")
        };
        let axioms = parsed.get(&qualified).ok_or_else(|| {
            format!(
                "lemma {qualified}: no #print axioms output (unknown constant? see probe at {})",
                probe_path.display()
            )
        })?;
        let c = classify(&qualified, axioms)?;
        match &c {
            Closure::Green(a) => {
                n_green += 1;
                report.push_str(&format!("GREEN  {qualified}  [{}]\n", a.join(", ")));
            }
            Closure::Sorry(a) => {
                n_sorry += 1;
                report.push_str(&format!("SORRY  {qualified}  [{}]\n", a.join(", ")));
            }
        }
        table.insert(l.clone(), c);
    }
    let sorry_txt = if n_sorry > 0 {
        format!("; {n_sorry} in flight (sorry)")
    } else {
        String::new()
    };
    let stamp = format!(
        "\\textcolor{{NoteGray}}{{\\footnotesize Marks derived live at render, {when}: \
         {n_green} lemmas kernel-closed within [propext, Classical.choice, Quot.sound]{sorry_txt} \
         (\\texttt{{lake env lean}} \\#print axioms; toolchain \\texttt{{{}}}; tree \\texttt{{{rev}{}}}).}}",
        toolchain.replace('_', "\\_"),
        if dirty { "+dirty" } else { "" }
    );
    Ok(Derivation {
        table,
        report,
        stamp,
    })
}

/// Merge two package derivations (main + aux) into one: tables union
/// (lemma keys are disjoint by construction — main lemmas resolve in the
/// PPLC namespace, aux lemmas are fully qualified), reports concatenate,
/// stamps join into one colophon line.
pub fn merge(mut a: Derivation, b: Derivation) -> Derivation {
    a.table.extend(b.table);
    a.report.push('\n');
    a.report.push_str(&b.report);
    if a.stamp.is_empty() {
        a.stamp = b.stamp;
    } else if !b.stamp.is_empty() {
        a.stamp.push_str(" \\enspace ");
        a.stamp.push_str(&b.stamp);
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_both_phrasings_and_wrapped_lists() {
        let out = "'PPLC.sound_ax' depends on axioms: [propext, Classical.choice,\n Quot.sound]\n\
                   'PPLC.triv' does not depend on any axioms\n\
                   'PPLC.wip' depends on axioms: [sorryAx, propext]\n";
        let m = parse_axioms(out);
        assert_eq!(
            m["PPLC.sound_ax"],
            vec!["propext", "Classical.choice", "Quot.sound"]
        );
        assert!(m["PPLC.triv"].is_empty());
        assert!(matches!(
            classify("PPLC.wip", &m["PPLC.wip"]).unwrap(),
            Closure::Sorry(_)
        ));
        assert!(matches!(
            classify("PPLC.sound_ax", &m["PPLC.sound_ax"]).unwrap(),
            Closure::Green(_)
        ));
        assert!(classify("bad", &["Classical.em".into()]).is_err());
    }
}
