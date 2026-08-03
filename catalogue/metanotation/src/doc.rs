//! Document assembly: rules schema, mark composition, TeX emission.
//!
//! Marks discipline (2026-07-17): the margin marks are
//! DERIVED, never hand-maintained. A rule declares which kernel lemmas
//! warrant it (`lemmas`), which named counterexample indicts its original
//! staging (`counterexample`), and optionally a vacuity witness
//! (`vacuous`); the mark glyphs and the witness line are composed from
//! those fields plus the live axiom-closure table (src/marks.rs). A rule
//! with none of the three renders unmarked — absence is honest.

use crate::marks::{Closure, LemmaTable};
use crate::{diff, render_side, tokenize, Op};
use serde::Deserialize;
use std::fmt::Write as _;

#[derive(Debug, Deserialize)]
pub struct RulesFile {
    pub meta: Meta,
    #[serde(rename = "rule")]
    pub rules: Vec<Rule>,
}

#[derive(Debug, Deserialize)]
pub struct Meta {
    pub title: String,
    pub subtitle: String,
    pub legend: String,
    pub colophon: String,
    /// output basename (default "BL-rules-diff") — a second rules file with
    /// its own basename renders to its own PDF without clobbering the first.
    #[serde(default)]
    pub basename: Option<String>,
    /// column headers (defaults: the original|amended pair of the main page).
    #[serde(default)]
    pub left_header: Option<String>,
    #[serde(default)]
    pub right_header: Option<String>,
    /// when true, the set of non-empty `tag` fields must equal the RuleTag
    /// enum extracted from the Lean catalogue (the extraction round-trip:
    /// a rule added in Lean fails the render until a row exists here).
    #[serde(default)]
    pub rule_enum_check: bool,
    /// sibling rules files (paths relative to this file's directory) whose
    /// tagged rows ALSO satisfy the round-trip — for enum tags whose human
    /// rows live on another page (the AG layer's Promise/Syzygy). This
    /// unions tags for the CHECK only; it deliberately does not decide the
    /// still-open page-fold question (rules.toml header, 2026-07-18).
    #[serde(default)]
    pub rule_enum_also: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub struct Rule {
    pub name: String,
    pub stratum: String,
    /// three-tier taxonomy (ratified 2026-07-18;
    /// names ratified the same day): 1 = CORE rule (semantic soundness —
    /// kernel content, not justified by unpacking); 2 = ADMISSIBLE rule
    /// (verified unpacking into core rules — a derivation, 1 node -> many);
    /// 3 = ALIAS rule (verified unpacking into a SINGLE admissible or core
    /// rule application, 1 node -> 1 node). Absent = not a proof rule (the
    /// sp-axiom). Renders as a word prefix in the cellhead's stratum slot.
    #[serde(default)]
    pub tier: Option<u8>,
    /// fourth category, GLUE (the TowerCitation rendering note,
    /// 2026-07-19): typing/conformance obligations on derivation edges —
    /// no conclusion judgement, warranted by the extension-edge DAG
    /// induction + the E3 acyclicity pass. Mutually exclusive with `tier`
    /// (a discipline is not one of the three rule sorts); renders as
    /// "edge discipline (glue)" and counts apart from the tiered rows.
    #[serde(default)]
    pub discipline: bool,
    /// optional per-profile tier split, rendered inside the tier badge
    /// (the QAGCompose case, leg-4 flag-4 ratified): free TeX like
    /// "admissible: ODE/discrete $\cdot$ core: SDE/GSHS --- derived from
    /// mechanism field-family population". DERIVED prose about how the
    /// staged tier is computed — never a stored second tier tag.
    #[serde(default)]
    pub tier_split: String,
    /// RuleTag constructor name in the Lean catalogue ("" = not a tagged
    /// rule: the sp-axiom, derived packagings, elaborated-away admissibles).
    #[serde(default)]
    pub tag: String,
    /// kernel soundness lemmas warranting the check mark (bare names,
    /// resolved in the PPLC namespace at derivation time).
    #[serde(default)]
    pub lemmas: Vec<String>,
    /// kernel soundness lemmas living in the AUXILIARY Lean package
    /// (qtsl-aux / QtslAux) — fully-qualified names, verified by
    /// a second per-package probe at derivation time. Same mark semantics
    /// as `lemmas`; the split only routes the probe.
    #[serde(default)]
    pub aux_lemmas: Vec<String>,
    /// TeX superscript qualifying the check (a proven-fragment tag).
    #[serde(default)]
    pub scope: String,
    /// TeX witness for the cross mark: the named counterexample against the
    /// rule's original staging. With `lemmas` too, renders x-then-check.
    #[serde(default)]
    pub counterexample: String,
    /// TeX witness for vacuous soundness (check with bottom superscript):
    /// the side-condition is realized uninhabited pending a ruling.
    /// Mutually exclusive with `lemmas`.
    #[serde(default)]
    pub vacuous: String,
    /// extra free-TeX witness prose, appended after the generated parts
    /// (or standing alone for unmarked rows).
    #[serde(default)]
    pub witness: String,
    /// paper-provenance content: verbatim, never normalized.
    /// Empty = the rule has no counterpart in the original paper; the row
    /// renders a grey marker on the left and the right column fully blue
    /// (all tokens are right-only — the honest diff of a new rule).
    pub original: String,
    pub amended: String,
    /// tool-voice annotation set under the row (grey, small).
    #[serde(default)]
    pub note: String,
}

/// Escape a Lean identifier for use inside \texttt.
fn tt_escape(s: &str) -> String {
    s.replace('_', "\\_")
}

/// Validate every row's tier against the ratified taxonomy (1..=3 or
/// absent). Run once after parse, before any render/check work.
pub fn validate_tiers(rf: &RulesFile) -> Result<(), String> {
    for r in &rf.rules {
        if let Some(t) = r.tier {
            if !(1..=3).contains(&t) {
                return Err(format!(
                    "rule {}: tier {} outside the ratified taxonomy (1 = core, \
                     2 = admissible, 3 = alias; omit for non-rules)",
                    r.name, t
                ));
            }
            if r.discipline {
                return Err(format!(
                    "rule {}: `discipline` (glue) and `tier` are mutually \
                     exclusive — an edge discipline is not one of the three \
                     rule sorts (drop the tier)",
                    r.name
                ));
            }
        }
    }
    Ok(())
}

/// The cellhead's stratum slot, tier-prefixed when the row carries one.
/// The ratified tier NAMES are the display (core/admissible/alias, plus
/// the glue category's "edge discipline"); the numeric tier stays
/// machine-side in the TOML. A non-empty `tier_split` renders inside the
/// badge, parenthesized after the tier word.
fn stratum_display(r: &Rule) -> String {
    let word = if r.discipline {
        "edge discipline (glue)"
    } else {
        match r.tier {
            Some(1) => "core rule",
            Some(2) => "admissible rule",
            Some(3) => "alias rule",
            _ => return r.stratum.clone(),
        }
    };
    let badge = if r.tier_split.is_empty() {
        word.to_string()
    } else {
        format!("{word} ({})", r.tier_split)
    };
    if r.stratum.is_empty() {
        badge
    } else {
        format!("{badge} --- {}", r.stratum)
    }
}

/// Compose the margin mark and the generated witness line for one rule.
/// `table` is None in declared mode (--no-verify): lemma presence is
/// trusted; in verify mode a lemma that came back sorry-carrying demotes
/// the check to a staged annotation.
pub fn compose_marks(r: &Rule, table: Option<&LemmaTable>) -> Result<(String, String), String> {
    let cited: Vec<&String> = r.lemmas.iter().chain(r.aux_lemmas.iter()).collect();
    if !r.vacuous.is_empty() && !cited.is_empty() {
        return Err(format!(
            "rule {}: `vacuous` and `lemmas`/`aux_lemmas` are mutually exclusive (a \
             vacuously-sound realization has no inhabited soundness lemma to cite)",
            r.name
        ));
    }
    let mut staged: Vec<&String> = Vec::new();
    if let Some(t) = table {
        for l in &cited {
            match t.get(*l) {
                Some(Closure::Green(_)) => {}
                Some(Closure::Sorry(_)) => staged.push(*l),
                None => {
                    return Err(format!(
                        "rule {}: lemma {} missing from the derivation table (internal)",
                        r.name, l
                    ))
                }
            }
        }
    }
    let checked = !cited.is_empty() && staged.is_empty();
    let cx = !r.counterexample.is_empty();
    let scope_sup = if r.scope.is_empty() {
        String::new()
    } else {
        format!("\\textsuperscript{{{}}}", r.scope)
    };

    let mark = if !r.vacuous.is_empty() {
        "\\cmark\\textsuperscript{$\\bot$}".to_string()
    } else {
        match (cx, checked) {
            (true, true) => format!("\\xmark$\\,\\to\\,$\\cmark{scope_sup}"),
            (false, true) => format!("\\cmark{scope_sup}"),
            (true, false) => "\\xmark".to_string(),
            (false, false) => String::new(),
        }
    };

    let mut parts: Vec<String> = Vec::new();
    if cx {
        parts.push(format!("\\xmark~{}", r.counterexample));
    }
    if checked {
        let names = cited
            .iter()
            .map(|l| format!("\\texttt{{{}}}", tt_escape(l)))
            .collect::<Vec<_>>()
            .join(", ");
        let scoped = if r.scope.is_empty() {
            format!("\\cmark~{names}")
        } else {
            format!("\\cmark{scope_sup}~{names}")
        };
        parts.push(scoped);
    } else if !staged.is_empty() {
        let names = staged
            .iter()
            .map(|l| format!("\\texttt{{{}}}", tt_escape(l)))
            .collect::<Vec<_>>()
            .join(", ");
        parts.push(format!("staged: {names} carries sorry — proof in flight"));
    }
    if !r.vacuous.is_empty() {
        parts.push(format!("\\cmark\\textsuperscript{{$\\bot$}}~{}", r.vacuous));
    }
    let mut witness = parts.join(" \\enspace$\\to$\\enspace ");
    if !r.witness.is_empty() {
        if witness.is_empty() {
            witness = r.witness.clone();
        } else {
            let _ = write!(witness, " — {}", r.witness);
        }
    }
    Ok((mark, witness))
}

/// The grey left-cell marker for rules with no counterpart in the paper.
const NO_COUNTERPART: &str =
    "\\textcolor{NoteGray}{\\itshape --- no rule in the April 2026 paper ---}";

pub fn build_document(
    rf: &RulesFile,
    table: Option<&LemmaTable>,
    stamp: &str,
) -> Result<String, String> {
    let mut body = String::new();
    for (idx, r) in rf.rules.iter().enumerate() {
        let a = tokenize(&r.original);
        let b = tokenize(&r.amended);
        let ops = diff(&a, &b);
        let left = if r.original.trim().is_empty() {
            NO_COUNTERPART.to_string()
        } else {
            render_side(&ops, Op::Left, "\\dfl")
        };
        // with an empty original every right token is Right-only: the row
        // renders fully blue, which is the honest diff of a new rule.
        let right = render_side(&ops, Op::Right, "\\dfr");
        let (mark, witness_line) = compose_marks(r, table)?;
        let marks = if mark.is_empty() {
            String::new()
        } else {
            format!("\\sidemarks{{{mark}}}")
        };
        let witness = if witness_line.is_empty() {
            String::new()
        } else {
            format!("\\witnessline{{{witness_line}}}")
        };
        let note = if r.note.is_empty() {
            String::new()
        } else {
            format!("\\rulenote{{{}}}", r.note)
        };
        write!(
            body,
            "{marks}\\begin{{cellbox}}\n\\cellhead{{{n}}}{{{name}}}{{{stratum}}}\n{left}\n\\end{{cellbox}}\n&\n\\begin{{cellbox}}\n\\cellheadright{{{witness}}}\n{right}\n{note}\n\\end{{cellbox}}\n\\\\\n\\rowgap\n",
            n = idx + 1,
            name = r.name,
            stratum = stratum_display(r),
        )
        .map_err(|e| e.to_string())?;
    }

    let left_header = rf.meta.left_header.clone().unwrap_or_else(|| {
        "\\normalsize\\textbf{original}\\enspace\\footnotesize (the April 2026 paper, verbatim)"
            .into()
    });
    let right_header = rf.meta.right_header.clone().unwrap_or_else(|| {
        "\\normalsize\\textbf{amended}\\enspace\\footnotesize (as realized in Lean)".into()
    });
    let colophon = if stamp.is_empty() {
        rf.meta.colophon.clone()
    } else {
        format!("{}\\par\\smallskip {stamp}", rf.meta.colophon)
    };
    let template = include_str!("../template.tex");
    Ok(template
        .replace("@@LEFTHEAD@@", &left_header)
        .replace("@@RIGHTHEAD@@", &right_header)
        .replace("@@TITLE@@", &rf.meta.title)
        .replace("@@SUBTITLE@@", &rf.meta.subtitle)
        .replace("@@LEGEND@@", &rf.meta.legend)
        .replace("@@COLOPHON@@", &colophon)
        .replace("@@BODY@@", &body))
}

/// Extract the RuleTag constructor names from the Lean catalogue source.
/// Scans the block between `inductive RuleTag where` and its `deriving`
/// line; every `|`-introduced identifier is a tag.
pub fn ruletag_enum(catalogue_src: &str) -> Result<Vec<String>, String> {
    let start = catalogue_src
        .find("inductive RuleTag where")
        .ok_or("RuleTag enum not found in catalogue source")?;
    let block = &catalogue_src[start..];
    let end = block
        .find("deriving")
        .ok_or("RuleTag enum: no `deriving` terminator")?;
    let mut tags = Vec::new();
    for line in block[..end].lines() {
        let line = line.split("--").next().unwrap_or("");
        for part in line.split('|').skip(1) {
            let ident: String = part
                .trim()
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !ident.is_empty() {
                tags.push(ident);
            }
        }
    }
    if tags.is_empty() {
        return Err("RuleTag enum: no constructors extracted".into());
    }
    Ok(tags)
}

/// The extraction round-trip: rows' tags vs the Lean enum, both directions.
/// `also_tags` carries tagged rows from `meta.rule_enum_also` sibling pages.
pub fn check_rule_enum(
    rf: &RulesFile,
    also_tags: &[String],
    enum_tags: &[String],
) -> Result<(), String> {
    let row_tags: Vec<&str> = rf
        .rules
        .iter()
        .filter(|r| !r.tag.is_empty())
        .map(|r| r.tag.as_str())
        .chain(also_tags.iter().map(|s| s.as_str()))
        .collect();
    let mut missing_rows: Vec<&String> = enum_tags
        .iter()
        .filter(|t| !row_tags.contains(&t.as_str()))
        .collect();
    let mut phantom_rows: Vec<&str> = row_tags
        .iter()
        .copied()
        .filter(|t| !enum_tags.iter().any(|e| e == t))
        .collect();
    // duplicates are also a defect (two rows claiming one tag)
    let mut seen = std::collections::HashSet::new();
    let dups: Vec<&str> = row_tags
        .iter()
        .copied()
        .filter(|t| !seen.insert(*t))
        .collect();
    missing_rows.sort();
    phantom_rows.sort();
    if missing_rows.is_empty() && phantom_rows.is_empty() && dups.is_empty() {
        return Ok(());
    }
    let mut msg = String::from("rule-enum round-trip FAILED:\n");
    if !missing_rows.is_empty() {
        let _ = writeln!(
            msg,
            "  Lean rules with no row (add rows): {}",
            missing_rows
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    if !phantom_rows.is_empty() {
        let _ = writeln!(
            msg,
            "  rows citing phantom tags: {}",
            phantom_rows.join(", ")
        );
    }
    if !dups.is_empty() {
        let _ = writeln!(msg, "  duplicate tags across rows: {}", dups.join(", "));
    }
    Err(msg)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::marks::Closure;
    use std::collections::HashMap;

    fn bare_rule(name: &str) -> Rule {
        Rule {
            name: name.into(),
            stratum: String::new(),
            tier: Some(1),
            discipline: false,
            tier_split: String::new(),
            tag: String::new(),
            lemmas: vec![],
            aux_lemmas: vec![],
            scope: String::new(),
            counterexample: String::new(),
            vacuous: String::new(),
            witness: String::new(),
            original: String::new(),
            amended: String::new(),
            note: String::new(),
        }
    }

    #[test]
    fn aux_lemmas_alone_earn_the_check_and_route_through_the_table() {
        let mut r = bare_rule("QSafetyBattery");
        r.aux_lemmas = vec!["Qtsl.Battery.sound_QSafetyBattery".into()];
        // declared mode: trusted
        let (mark, witness) = compose_marks(&r, None).unwrap();
        assert!(mark.contains("\\cmark"));
        assert!(witness.contains("sound\\_QSafetyBattery"));
        // verify mode: green closure keeps the check…
        let mut t: HashMap<String, Closure> = HashMap::new();
        t.insert(
            "Qtsl.Battery.sound_QSafetyBattery".into(),
            Closure::Green(vec![]),
        );
        let (mark, _) = compose_marks(&r, Some(&t)).unwrap();
        assert!(mark.contains("\\cmark"));
        // …a sorry-carrying closure demotes it
        t.insert(
            "Qtsl.Battery.sound_QSafetyBattery".into(),
            Closure::Sorry(vec!["sorryAx".into()]),
        );
        let (mark, witness) = compose_marks(&r, Some(&t)).unwrap();
        assert!(mark.is_empty());
        assert!(witness.contains("proof in flight"));
        // …and a missing table entry is an error, aux lemmas included
        let empty: HashMap<String, Closure> = HashMap::new();
        assert!(compose_marks(&r, Some(&empty)).is_err());
    }

    #[test]
    fn vacuous_excludes_aux_lemmas_too() {
        let mut r = bare_rule("X");
        r.vacuous = "witness".into();
        r.aux_lemmas = vec!["A.b".into()];
        assert!(compose_marks(&r, None).is_err());
    }
}
