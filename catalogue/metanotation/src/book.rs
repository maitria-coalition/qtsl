//! book.rs — the literate rule catalogue.
//!
//! Per-rule subsections: the Steele-metanotation rule (joined from the
//! existing rules pages — never duplicated), the Lean statement (extracted
//! from source by decl name at every render), Lean verifier receipts (cited
//! from the ed25519 receipt store, signature-verified at render, staleness
//! badged against `book/bindings.toml`), the HOL statement or its loudly
//! rendered absence, documentary HOL receipts, the Isabelle open question,
//! and a hand-authored proof (`book/proofs/<id>.tex`), genre by tier.
//! Design: book/DESIGN.md. Nothing here runs Lean — receipts are
//! citations; verification happens where the gate machinery runs.

use crate::doc::RulesFile;
use serde::Deserialize;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

// ============================ book.toml ============================

#[derive(Debug, Deserialize)]
pub struct BookFile {
    pub meta: BookMeta,
    /// default-empty: after the sharding, every entry may live in a
    /// book.toml.d/ fragment and book.toml may carry [meta] alone.
    #[serde(rename = "rule", default)]
    pub rules: Vec<BookRule>,
    /// dashboard-only Lean-coverage entries: rules whose full literate
    /// section (commentary, proof, HOL) is not yet authored, but whose Lean
    /// mechanization exists and deserves honest dashboard glyphs. Same
    /// binding/receipt machinery as full entries; renders no body section.
    #[serde(rename = "coverage", default)]
    pub coverage: Vec<Coverage>,
}

#[derive(Debug, Deserialize)]
pub struct BookMeta {
    pub title: String,
    pub subtitle: String,
    /// TeX, rendered as the front-matter preface (cold-reader-facing: what
    /// the calculus is, what a certificate is, what receipts mean, why a
    /// green cell deserves trust).
    pub preface: String,
    /// TeX: the grey introductory paragraph under the Coverage Dashboard
    /// heading (where the ingredients-and-sources content lives).
    pub dashboard_intro: String,
    /// TeX: the no-signed-HOL-store note, referenced from HOL receipt cells.
    pub hol_store_note: String,
    /// rules-page sources joined for cells + the dashboard (crate-relative).
    pub pages: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub struct BookRule {
    /// stable id — proof file key, single-rule render selector.
    pub id: String,
    /// which rules page carries the row (crate-relative path, ∈ meta.pages).
    pub source: String,
    /// the row's `name` in that page.
    pub row: String,
    /// proof file, crate-relative (book/proofs/<id>.tex by convention).
    pub proof: String,
    /// TeX: substantial reader-facing prose right after the rule display —
    /// what the rule does, when a producer uses it, what the checker
    /// recomputes, what would break without each hypothesis.
    #[serde(default)]
    pub commentary: String,
    /// TeX: the book's own note for this rule. The joined row's `note` is
    /// NEVER rendered here (the pages' notes are internal-register; the
    /// book's reader is external) — this field is the replacement.
    #[serde(default)]
    pub note: String,
    /// tier-3 rules: the alias target, named + coloured in the header.
    #[serde(default)]
    pub alias_target: String,
    /// true = the cited theorems warrant the rule *conditionally* (named
    /// hypothesis gaps, or a proven fragment/profile) — same semantics as
    /// the coverage flag, kept on graduation so the dashboard's
    /// hyp-flavoured check never silently widens into a plain one. The
    /// specifics live in the rule's commentary and its page row.
    #[serde(default)]
    pub conditional: bool,
    /// optional superscript label for the conditional mark: set it when the
    /// conditional warrant is a single crisp profile/fragment name
    /// ("DTMC", "finite"), and the dashboard renders \dcond[DTMC] instead
    /// of the generic \dcond ("hyp"). Meaningful only with
    /// `conditional = true` (loud error otherwise); a warrant that is a
    /// bag of side conditions keeps the bare flag.
    #[serde(default)]
    pub conditional_label: String,
    /// optional comparator-coverage TeX line; empty = the honest default
    /// ("no comparator fixture exercises this rule").
    #[serde(default)]
    pub comparator: String,
    /// the correspondence dictionary (the interim, reviewer-grade tooth of
    /// the correspondence layer): TeX prose stating HOW the bound Lean
    /// statements interpret the Steele display — display metavariable ↦
    /// Lean binder, each display hypothesis ↦ the premise or side
    /// condition carrying it, the display conclusion ↦ the goal, and any
    /// deliberate width difference named. `bind` records the
    /// (Steele-cell sha, statement-set sha, prose sha) triple the prose
    /// was certified against (pass-marker semantics: kept verbatim across
    /// binds; re-stamped only by --recertify or on first bind); the
    /// render badges the block amber the moment any side moves. Empty =
    /// not yet certified, rendered as a loud absence wherever the rule
    /// binds Lean.
    #[serde(default)]
    pub correspondence: String,
    #[serde(default)]
    pub lean: Vec<LeanRef>,
    pub hol: HolRef,
}

/// A rule row's dashboard-only Lean coverage (no book section yet).
#[derive(Debug, Deserialize)]
pub struct Coverage {
    /// which rules page carries the row (crate-relative path, ∈ meta.pages).
    pub source: String,
    /// the row's `name` in that page.
    pub row: String,
    /// true = the cited theorems warrant the rule *conditionally* — named
    /// hypothesis gaps, or a proven fragment/profile of the rule as
    /// catalogued. The dashboard renders the hyp-flavoured check; the named
    /// hypotheses/profile live in the rule's own page (witness prose).
    #[serde(default)]
    pub conditional: bool,
    /// optional superscript label for the conditional mark (see the
    /// BookRule field of the same name): a single crisp profile/fragment
    /// name renders as \dcond[NAME]; empty keeps the generic "hyp".
    #[serde(default)]
    pub conditional_label: String,
    #[serde(rename = "lean", default)]
    pub lean: Vec<LeanRef>,
}

fn default_package() -> String {
    "main".to_string()
}

#[derive(Debug, Deserialize)]
pub struct LeanRef {
    /// Lean package the module lives in ("main" = the Qtsl
    /// package; "qtsl-aux" = the QtslAux sibling). Written into
    /// the binding for provenance; sources resolve via `src` either way.
    #[serde(default = "default_package")]
    pub package: String,
    /// Lean module name receipts attest (e.g. "Qtsl.Soundness").
    pub module: String,
    /// module source path, crate-relative.
    pub src: String,
    /// TeX prose rendered before this block's decls (e.g. the meaning-binding
    /// walkthrough for checker definitions).
    #[serde(default)]
    pub intro: String,
    /// decls to quote statement-only, in print order (signatures cut at the
    /// proof/definition body).
    #[serde(default)]
    pub decls: Vec<String>,
    /// decls to quote with their FULL definition bodies — for definitions
    /// whose meaning the book must bind, not merely name.
    #[serde(default)]
    pub full_decls: Vec<String>,
}

#[derive(Debug, Deserialize)]
pub struct HolRef {
    /// "ported" | "absent" | "out-of-scope"
    pub status: String,
    #[serde(default)]
    pub script: String,
    #[serde(default)]
    pub theory: String,
    /// HOL decl blocks to quote: "Definition foo_def" / "Theorem bar".
    #[serde(default)]
    pub decls: Vec<String>,
    /// TeX: documentary receipt citation (census rows, landing evidence).
    #[serde(default)]
    pub receipt: String,
    /// TeX: the loud reason when status != "ported".
    #[serde(default)]
    pub reason: String,
}

// ========================== bindings.toml ==========================

#[derive(Debug, Deserialize, Default)]
pub struct Bindings {
    #[serde(rename = "module", default)]
    pub modules: Vec<ModuleBind>,
    #[serde(rename = "statement", default)]
    pub statements: Vec<StmtBind>,
    #[serde(rename = "hol_file", default)]
    pub hol_files: Vec<HolBind>,
    #[serde(rename = "correspondence", default)]
    pub correspondences: Vec<CorrBind>,
}

#[derive(Debug, Deserialize)]
pub struct ModuleBind {
    pub module: String,
    /// Lean package ("main" | "qtsl-aux"); see LeanRef.package.
    #[serde(default = "default_package")]
    pub package: String,
    /// SHA-256 of the attested build artefact — or EMPTY when the module is
    /// source-bound only (no build attestation exists yet): statements stay
    /// hash-bound to source, receipts can never be judged current.
    pub olean_sha256: String,
    pub olean_provenance: String,
    pub source_git_blob: String,
}

#[derive(Debug, Deserialize)]
pub struct StmtBind {
    pub module: String,
    pub decl: String,
    pub sha256: String,
}

#[derive(Debug, Deserialize)]
pub struct HolBind {
    pub script: String,
    pub git_blob: String,
}

/// The correspondence-certification triple: what a rule entry's
/// correspondence prose was certified against. Machine-written by `bind`
/// into the entry's own bindings shard; kept verbatim across binds
/// (pass-marker semantics — a bind run for other reasons must never
/// silently launder an unreviewed change into "certified") and re-stamped
/// only on first bind of a new dictionary or by an explicit
/// `bind --recertify <entry|all>`.
#[derive(Debug, Deserialize, Clone)]
pub struct CorrBind {
    /// the book entry (rule id) this triple certifies.
    pub entry: String,
    /// sha256 of the roster row's `amended` cell at certification.
    pub steele_sha256: String,
    /// sha256 of the entry's statement-row set at certification — sorted
    /// "module decl sha" lines, one per bound decl (see
    /// `statements_digest`).
    pub statements_sha256: String,
    /// sha256 of the correspondence prose itself at certification (an
    /// edited dictionary must re-certify — text and pair travel together).
    pub prose_sha256: String,
}

/// Digest of an entry's statement-row set — the statement side of the
/// correspondence triple. Order-independent: rows sort before hashing.
pub fn statements_digest(rows: &[(String, String, String)]) -> String {
    let mut lines: Vec<String> = rows
        .iter()
        .map(|(m, d, s)| format!("{m} {d} {s}\n"))
        .collect();
    lines.sort();
    lines.dedup();
    sha256_hex(lines.concat().as_bytes())
}

/// The render-time verdict on a rule's correspondence certification.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum CorrState {
    /// no dictionary written (honest absence).
    Absent,
    /// prose exists but no recorded triple — bind has not stamped it.
    Unrecorded,
    /// a recorded triple exists but a side moved since certification.
    Drifted {
        steele: bool,
        statements: bool,
        prose: bool,
    },
    /// recorded triple matches all three current hashes.
    Certified,
}

/// Judge a rule's correspondence state from the recorded triple and the
/// three current hashes. Pure — the testable core of the badge logic.
pub fn corr_state(
    has_prose: bool,
    recorded: Option<&CorrBind>,
    steele_now: &str,
    statements_now: &str,
    prose_now: &str,
) -> CorrState {
    if !has_prose {
        return CorrState::Absent;
    }
    match recorded {
        None => CorrState::Unrecorded,
        Some(r) => {
            let steele = r.steele_sha256 != steele_now;
            let statements = r.statements_sha256 != statements_now;
            let prose = r.prose_sha256 != prose_now;
            if steele || statements || prose {
                CorrState::Drifted {
                    steele,
                    statements,
                    prose,
                }
            } else {
                CorrState::Certified
            }
        }
    }
}

// ====================== Lean statement extraction ======================

/// Decl kinds we can extract. Kind is detected from the source line.
const LEAN_DECL_KEYWORDS: &[&str] = &[
    "theorem",
    "def",
    "structure",
    "inductive",
    "abbrev",
    "lemma",
];

/// Extract `decl`'s doc comment + statement (signature without proof body)
/// from Lean source. Termination: `theorem`/`def`/`abbrev`/`lemma` cut at
/// the first top-level `:= by` / `:=` / trailing ` where`; `structure`/
/// `inductive` collect the whole block (fields are the rule's payload) up
/// to the next column-0 line.
pub fn extract_lean_decl(source: &str, decl: &str) -> Result<String, String> {
    extract_lean_decl_with(source, decl, false)
}

/// Extract `decl` with its FULL body: doc comment + everything through the
/// last line before the next column-0 construct. For definitions whose
/// meaning the book binds by display (the reader must see the body).
pub fn extract_lean_decl_full(source: &str, decl: &str) -> Result<String, String> {
    extract_lean_decl_with(source, decl, true)
}

fn extract_lean_decl_with(source: &str, decl: &str, full: bool) -> Result<String, String> {
    let lines: Vec<&str> = source.lines().collect();
    let mut decl_line: Option<(usize, &str)> = None;
    for (i, l) in lines.iter().enumerate() {
        let t = l.trim_start();
        // top-level decls only (column 0, modulo `private `)
        if l.starts_with(char::is_whitespace) {
            continue;
        }
        let t = t.strip_prefix("private ").unwrap_or(t);
        for kw in LEAN_DECL_KEYWORDS {
            if let Some(rest) = t.strip_prefix(kw) {
                let rest = rest.trim_start();
                if rest.starts_with(decl)
                    && rest[decl.len()..]
                        .chars()
                        .next()
                        .map(|c| !c.is_alphanumeric() && c != '_')
                        .unwrap_or(true)
                {
                    decl_line = Some((i, kw));
                    break;
                }
            }
        }
        if decl_line.is_some() {
            break;
        }
    }
    let (start, kind) =
        decl_line.ok_or_else(|| format!("decl {decl}: not found at top level in source"))?;

    // include the contiguous doc comment (/-- … -/) ending on the line above
    let mut first = start;
    if start > 0 && lines[start - 1].trim_end().ends_with("-/") {
        let mut j = start - 1;
        loop {
            if lines[j].trim_start().starts_with("/--") {
                first = j;
                break;
            }
            if j == 0 {
                break;
            }
            j -= 1;
        }
    }

    let structural = full || matches!(kind, "structure" | "inductive");
    let mut out: Vec<String> = Vec::new();
    for l in lines.iter().take(start).skip(first) {
        out.push((*l).to_string());
    }
    for (n, l) in lines.iter().enumerate().skip(start) {
        if structural {
            if n > start && !l.is_empty() && !l.starts_with(char::is_whitespace) {
                break; // next top-level construct
            }
            out.push((*l).to_string());
        } else {
            // cut markers, in order of specificity
            if let Some(p) = l.find(":= by") {
                let head = l[..p].trim_end();
                if !head.is_empty() {
                    out.push(head.to_string());
                }
                return Ok(finish(out));
            }
            if let Some(p) = l.find(":=") {
                let head = l[..p].trim_end();
                if !head.is_empty() {
                    out.push(head.to_string());
                }
                return Ok(finish(out));
            }
            if let Some(head) = l.trim_end().strip_suffix(" where") {
                out.push(head.trim_end().to_string());
                return Ok(finish(out));
            }
            out.push((*l).to_string());
        }
    }
    if structural {
        // trim trailing blank lines
        while out.last().map(|s| s.trim().is_empty()).unwrap_or(false) {
            out.pop();
        }
        return Ok(finish(out));
    }
    Err(format!(
        "decl {decl}: no statement terminator (:= / where) found"
    ))
}

fn finish(lines: Vec<String>) -> String {
    let mut s = lines.join("\n");
    while s.ends_with('\n') {
        s.pop();
    }
    s
}

// ======================= HOL statement extraction =======================

/// Extract a HOL4 script block: "Definition name" → through its `End`;
/// "Theorem name" → statement only (up to the line before `Proof`).
pub fn extract_hol_decl(source: &str, spec: &str) -> Result<String, String> {
    let (kw, name) = spec.split_once(' ').ok_or_else(|| {
        format!("HOL decl spec '{spec}': expected 'Definition foo' / 'Theorem bar'")
    })?;
    if !matches!(kw, "Definition" | "Theorem") {
        return Err(format!("HOL decl spec '{spec}': unknown block kind {kw}"));
    }
    let lines: Vec<&str> = source.lines().collect();
    let mut start = None;
    for (i, l) in lines.iter().enumerate() {
        if let Some(rest) = l.strip_prefix(kw) {
            let rest = rest.trim_start();
            if rest.starts_with(name)
                && rest[name.len()..]
                    .chars()
                    .next()
                    .map(|c| c == ':' || c == '[')
                    .unwrap_or(false)
            {
                start = Some(i);
                break;
            }
        }
    }
    let start = start.ok_or_else(|| format!("HOL block {kw} {name}: not found"))?;
    let mut out = Vec::new();
    for l in &lines[start..] {
        match kw {
            "Definition" => {
                out.push((*l).to_string());
                if l.trim() == "End" {
                    return Ok(finish(out));
                }
            }
            _ => {
                if l.trim() == "Proof" {
                    while out
                        .last()
                        .map(|s: &String| s.trim().is_empty())
                        .unwrap_or(false)
                    {
                        out.pop();
                    }
                    return Ok(finish(out));
                }
                out.push((*l).to_string());
            }
        }
    }
    Err(format!("HOL block {kw} {name}: unterminated"))
}

// ============================ hashing ============================

pub fn sha256_hex(bytes: &[u8]) -> String {
    // Shell out to sha256sum: no crypto dep for a build tool, and the same
    // binary the receipt pipeline itself trusts on this box.
    use std::io::Write as _;
    let mut child = Command::new("sha256sum")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("sha256sum not found");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(bytes)
        .expect("write to sha256sum");
    let out = child.wait_with_output().expect("sha256sum run");
    String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .next()
        .expect("sha256sum output")
        .to_string()
}

/// git blob sha of a file's current content (content-addressed; index-independent).
pub fn git_blob_sha(path: &Path) -> Result<String, String> {
    let out = Command::new("git")
        .args(["hash-object", "--"])
        .arg(path)
        .output()
        .map_err(|e| format!("git hash-object: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "git hash-object {}: {}",
            path.display(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

// ============================ receipts ============================

#[derive(Debug, Clone)]
pub struct ReceiptInfo {
    pub sig16: String,
    pub module: String,
    pub olean_sha256: String,
    pub layers: Vec<String>,
    pub node: String,
    pub ts: String,
    /// signer ed25519 pubkey, hex (rendered by fingerprint — the
    /// content-addressed attestation identity; node labels stay off the page).
    pub signer: String,
    pub trust: String, // "TRUSTED (root 'x')" | "valid, untrusted" | error text
}

/// Scan the receipt store for receipts on `modules`, verifying each
/// signature via the companion `lean-receipt` tool (the receipt authority —
/// this generator deliberately holds no signature code of its own).
pub fn scan_receipts(
    store: &Path,
    roots: &Path,
    modules: &HashSet<String>,
) -> Result<Vec<ReceiptInfo>, String> {
    if !store.is_dir() {
        return Err(format!("receipt store {} not found", store.display()));
    }
    let mut found = Vec::new();
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(store)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    for d in dirs {
        let mut files: Vec<PathBuf> = std::fs::read_dir(&d)
            .map_err(|e| e.to_string())?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map(|x| x == "cbor").unwrap_or(false))
            .collect();
        files.sort();
        for f in files {
            let out = Command::new("lean-receipt")
                .arg("verify")
                .arg(&f)
                .env("LEAN_RECEIPT_ROOTS", roots)
                .output()
                .map_err(|e| format!("lean-receipt verify: cannot launch: {e} — install the tool or render with --no-receipts"))?;
            let text = String::from_utf8_lossy(&out.stdout).to_string()
                + &String::from_utf8_lossy(&out.stderr);
            let field = |k: &str| -> String {
                text.lines()
                    .find_map(|l| l.strip_prefix(k))
                    .map(|v| v.trim().to_string())
                    .unwrap_or_default()
            };
            let module = field("module:");
            if !modules.contains(&module) {
                continue;
            }
            let node_ts = field("node:");
            let (node, ts) = match node_ts.split_once("ts:") {
                Some((n, t)) => (n.trim().to_string(), t.trim().to_string()),
                None => (node_ts.clone(), String::new()),
            };
            let sigline = field("signature:");
            let trust = if !out.status.success() {
                format!("VERIFY FAILED: {}", sigline)
            } else {
                sigline
            };
            found.push(ReceiptInfo {
                sig16: f
                    .file_stem()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default(),
                module,
                olean_sha256: field("olean_sha256:"),
                layers: field("layers:")
                    .split('+')
                    .map(|s| s.to_string())
                    .filter(|s| !s.is_empty())
                    .collect(),
                node,
                ts,
                signer: field("signer:"),
                trust,
            });
        }
    }
    found.sort_by(|a, b| a.ts.cmp(&b.ts));
    Ok(found)
}

/// The four gate layers, in the order the verification pipeline runs them.
pub const GATE_LAYERS: &[(&str, &str)] = &[
    ("build", "lake build (elaboration)"),
    ("replay", "leanchecker (official kernel replay)"),
    ("hardened", "safe\\_verify (hardened screen)"),
    ("decorrelated", "lean4export + nanoda (decorrelated kernel)"),
];

// ============================ statuses ============================

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Drift {
    Fresh,
    ModuleMoved,      // source blob drifted, statements intact (AMBER)
    StatementChanged, // extracted statement sha mismatch (RED)
}

pub struct RuleRender {
    pub id: String,
    pub tex: String,
    pub dash: DashRow,
}

#[derive(Debug, Default, Clone)]
pub struct DashRow {
    pub name: String,
    pub tier: Option<u8>,
    pub lean_bound: bool,
    pub drift: Option<Drift>,
    /// coverage-entry flag: statements bound and fresh, but the cited
    /// theorems warrant the rule conditionally (hypothesis gaps / fragment).
    pub conditional: bool,
    /// optional named-profile superscript for the conditional mark
    /// (\dcond[DTMC]); empty renders the generic "hyp".
    pub conditional_label: String,
    /// per gate layer: 2 = current receipt, 1 = stale-only, 0 = none
    pub layer_state: [u8; 4],
    /// correspondence certification: 2 = certified against the current
    /// texts, 1 = prose present but uncertified or drifted, 0 = none.
    pub corr: u8,
    pub hol: String, // "ported" | "absent" | "out-of-scope" | "—"
    pub hol_receipt: bool,
    pub proof: bool,
}

/// Extract one decl and judge its drift against the bindings. Shared by the
/// full book sections and the dashboard-only coverage entries.
pub fn decl_drift(
    source: &str,
    lean: &LeanRef,
    decl: &str,
    full: bool,
    bindings: &Bindings,
    module_moved: bool,
) -> Result<(String, Drift), String> {
    let stmt = if full {
        extract_lean_decl_full(source, decl)
    } else {
        extract_lean_decl(source, decl)
    }?;
    let sha = sha256_hex(stmt.as_bytes());
    let bound = bindings
        .statements
        .iter()
        .find(|s| s.module == lean.module && s.decl == decl);
    let drift = match bound {
        None => Drift::StatementChanged, // unbound statement: treat as loud
        Some(b) if b.sha256 != sha => Drift::StatementChanged,
        Some(_) if module_moved => Drift::ModuleMoved,
        Some(_) => Drift::Fresh,
    };
    Ok((stmt, drift))
}

/// Credit the four gate layers from the store's receipts for one module.
/// A receipt matching the bound build is current (2); any other receipt for
/// the module is stale-only (1). A module with NO attested build (empty
/// bound olean) can never have a current receipt — stale-only at most.
pub fn credit_layers(
    receipts: &[ReceiptInfo],
    module: &str,
    bound_olean: &str,
    layer_state: &mut [u8; 4],
) {
    for r in receipts.iter().filter(|r| r.module == module) {
        let current = !bound_olean.is_empty() && r.olean_sha256 == bound_olean;
        for (i, (l, _)) in GATE_LAYERS.iter().enumerate() {
            if r.layers.iter().any(|x| x == l) {
                if current {
                    layer_state[i] = 2;
                } else if layer_state[i] < 1 {
                    layer_state[i] = 1;
                }
            }
        }
    }
}

/// Dashboard row for a coverage entry: joins the rules-page row, extracts
/// and drift-judges every cited decl, credits receipt layers. No TeX body.
/// A conditional-mark label ("DTMC") is meaningful only on a conditional
/// row, and it lands inside a LaTeX optional argument — reject anything
/// that would escape the bracket or smuggle markup. Shared by the rule
/// and coverage paths.
fn validate_conditional_label(id: &str, conditional: bool, label: &str) -> Result<(), String> {
    if label.is_empty() {
        return Ok(());
    }
    if !conditional {
        return Err(format!(
            "{id}: conditional_label = \"{label}\" without conditional = true — \
             the label names what the conditional warrant covers; set the flag \
             or drop the label"
        ));
    }
    if !label
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.' | ' '))
    {
        return Err(format!(
            "{id}: conditional_label \"{label}\" — labels render inside \
             \\dcond[...] and are confined to [A-Za-z0-9+-. ]"
        ));
    }
    Ok(())
}

pub fn coverage_dash(
    ctx: &BookCtx,
    cov: &Coverage,
    pages: &BTreeMap<String, RulesFile>,
    bindings: &Bindings,
    receipts: &[ReceiptInfo],
) -> Result<(String, DashRow), String> {
    let page = pages.get(&cov.source).ok_or_else(|| {
        format!(
            "coverage {}: source page {} not in meta.pages",
            cov.row, cov.source
        )
    })?;
    let row = page
        .rules
        .iter()
        .find(|r| r.name == cov.row)
        .ok_or_else(|| format!("coverage: row '{}' not found in {}", cov.row, cov.source))?;
    if cov.lean.is_empty() {
        return Err(format!(
            "coverage {}: no [[coverage.lean]] block — an empty coverage \
             entry claims nothing; delete it",
            cov.row
        ));
    }
    validate_conditional_label(&cov.row, cov.conditional, &cov.conditional_label)?;
    let mut dash = DashRow {
        name: row.name.clone(),
        tier: row.tier,
        lean_bound: true,
        conditional: cov.conditional,
        conditional_label: cov.conditional_label.clone(),
        hol: "—".to_string(),
        ..Default::default()
    };
    let mut worst = Drift::Fresh;
    for lean in &cov.lean {
        let src_path = ctx.crate_root.join(&lean.src);
        let source = std::fs::read_to_string(&src_path)
            .map_err(|e| format!("coverage {}: cannot read {}: {e}", cov.row, lean.src))?;
        let mb = bindings
            .modules
            .iter()
            .find(|m| m.module == lean.module)
            .ok_or_else(|| {
                format!(
                    "coverage {}: module {} has no binding — run qtsl-book bind",
                    cov.row, lean.module
                )
            })?;
        let module_moved = git_blob_sha(&src_path)? != mb.source_git_blob;
        let quoted: Vec<(&String, bool)> = lean
            .decls
            .iter()
            .map(|d| (d, false))
            .chain(lean.full_decls.iter().map(|d| (d, true)))
            .collect();
        for (d, full) in quoted {
            let (_stmt, drift) = decl_drift(&source, lean, d, full, bindings, module_moved)
                .map_err(|e| format!("coverage {} / {}: {e}", cov.row, lean.src))?;
            if drift_rank(drift) > drift_rank(worst) {
                worst = drift;
            }
        }
        credit_layers(
            receipts,
            &lean.module,
            &mb.olean_sha256,
            &mut dash.layer_state,
        );
    }
    dash.drift = Some(worst);
    Ok((format!("{}::{}", cov.source, cov.row), dash))
}

// ============================ TeX helpers ============================

fn tex_verbatim_block(env: &str, text: &str) -> String {
    // Verbatim content passes through untouched; guard the one impossible
    // string (the environment's own \end).
    let guard = format!("\\end{{{env}}}");
    assert!(
        !text.contains(&guard),
        "verbatim payload contains {guard} — cannot embed"
    );
    format!("\\begin{{{env}}}\n{text}\n\\end{{{env}}}\n")
}

fn badge(color: &str, text: &str) -> String {
    format!("\\badge{{{color}}}{{{text}}}")
}

// ============================ the build ============================

pub struct BookCtx {
    pub crate_root: PathBuf,
    pub store: PathBuf,
    pub roots: PathBuf,
    pub consult_receipts: bool,
}

pub fn load_pages(
    crate_root: &Path,
    pages: &[String],
) -> Result<BTreeMap<String, RulesFile>, String> {
    let mut m = BTreeMap::new();
    for p in pages {
        let raw = std::fs::read_to_string(crate_root.join(p))
            .map_err(|e| format!("cannot read page {p}: {e}"))?;
        let rf: RulesFile =
            toml::from_str(&raw).map_err(|e| format!("page {p} parse error: {e}"))?;
        m.insert(p.clone(), rf);
    }
    Ok(m)
}

// ==================== fragment loading (the fan seam) ====================

/// A fragment file under `book/book.toml.d/`: exactly one [[rule]] xor one
/// [[coverage]] entry, byte-for-byte the same schema those entries have in
/// book.toml. The fan doctrine: parallel authors own disjoint
/// fragment files — one file per catalogue row — so the book's spine never
/// becomes a merge bottleneck, and graduating a coverage entry to a full
/// rule section is an edit to that row's own file, never to a shared one.
#[derive(Debug, Deserialize)]
pub struct BookFragment {
    #[serde(rename = "rule", default)]
    pub rules: Vec<BookRule>,
    #[serde(rename = "coverage", default)]
    pub coverage: Vec<Coverage>,
}

/// Filename stem for an entry key: ASCII alphanumerics, '_' and '-' kept,
/// every other char mapped to '_' — predictable, no collapsing. Rule ids
/// are required to be filename-safe already; coverage rows (which may
/// carry TeX, e.g. `$\wedge$I`) sanitize through this.
pub fn sanitize_frag_stem(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn frag_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("read {}: {e}", dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().map(|x| x == "toml").unwrap_or(false))
        .collect();
    v.sort();
    Ok(v)
}

/// Load book.toml + every fragment in book.toml.d/ (sorted by filename —
/// deterministic merge order), then run the union's uniqueness checks:
/// rule ids unique; each (source, row) claimed by at most one entry of
/// either kind. Section ORDER is not encounter order — see
/// `canonical_rule_order`.
pub fn load_book_dir(book_dir: &Path) -> Result<(BookFile, Bindings), String> {
    let raw = std::fs::read_to_string(book_dir.join("book.toml"))
        .map_err(|e| format!("cannot read book.toml: {e}"))?;
    let mut bf: BookFile =
        toml::from_str(&raw).map_err(|e| format!("book.toml parse error: {e}"))?;

    let frag_dir = book_dir.join("book.toml.d");
    if frag_dir.is_dir() {
        for f in frag_files(&frag_dir)? {
            let name = f
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default();
            let raw = std::fs::read_to_string(&f)
                .map_err(|e| format!("cannot read fragment {name}: {e}"))?;
            let frag: BookFragment =
                toml::from_str(&raw).map_err(|e| format!("fragment {name} parse error: {e}"))?;
            let stem = f
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default();
            match (frag.rules.len(), frag.coverage.len()) {
                (1, 0) => {
                    let r = frag.rules.into_iter().next().expect("len checked");
                    if r.id.is_empty()
                        || !r
                            .id
                            .chars()
                            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
                    {
                        return Err(format!(
                            "fragment {name}: rule id '{}' is not filename-safe \
                             ([A-Za-z0-9_-] only) — fragment-borne rules name their file",
                            r.id
                        ));
                    }
                    if stem != r.id {
                        return Err(format!(
                            "fragment {name}: file stem must equal the rule id '{}' \
                             (one entry per file, the file named for it)",
                            r.id
                        ));
                    }
                    bf.rules.push(r);
                }
                (0, 1) => {
                    let c = frag.coverage.into_iter().next().expect("len checked");
                    let want = sanitize_frag_stem(&c.row);
                    if stem != want {
                        return Err(format!(
                            "fragment {name}: file stem must be '{want}' \
                             (the sanitized row name of '{}')",
                            c.row
                        ));
                    }
                    bf.coverage.push(c);
                }
                (r, c) => {
                    return Err(format!(
                        "fragment {name}: exactly one [[rule]] xor one [[coverage]] entry \
                         per fragment (found {r} rule(s), {c} coverage entr(y/ies))"
                    ));
                }
            }
        }
    }

    let mut ids = HashSet::new();
    for r in &bf.rules {
        if !ids.insert(r.id.clone()) {
            return Err(format!(
                "duplicate rule id '{}' across book.toml + fragments",
                r.id
            ));
        }
    }
    let mut rows: HashSet<(String, String)> = HashSet::new();
    for (src, row) in bf
        .rules
        .iter()
        .map(|r| (&r.source, &r.row))
        .chain(bf.coverage.iter().map(|c| (&c.source, &c.row)))
    {
        if !rows.insert((src.clone(), row.clone())) {
            return Err(format!(
                "row {src}::{row} claimed twice across book.toml + fragments (a row \
                 carries one [[rule]] or one [[coverage]] entry, never two)"
            ));
        }
    }

    let bindings = load_bindings_dir(book_dir)?;
    Ok((bf, bindings))
}

/// Load bindings.toml + bindings.toml.d/*.toml (machine-maintained
/// per-entry statement shards — see `qtsl-book bind`), merged. Exact
/// duplicate rows collapse (two entries citing one decl is legitimate); a
/// (module, decl) bound with two different hashes is a defect, since the
/// render's lookup is by that key alone.
pub fn load_bindings_dir(book_dir: &Path) -> Result<Bindings, String> {
    let mut b: Bindings = match std::fs::read_to_string(book_dir.join("bindings.toml")) {
        Ok(s) => toml::from_str(&s).map_err(|e| format!("bindings.toml parse error: {e}"))?,
        Err(_) => Bindings::default(),
    };
    let d = book_dir.join("bindings.toml.d");
    if d.is_dir() {
        for f in frag_files(&d)? {
            let raw = std::fs::read_to_string(&f)
                .map_err(|e| format!("cannot read {}: {e}", f.display()))?;
            let frag: Bindings = toml::from_str(&raw)
                .map_err(|e| format!("bindings fragment {} parse error: {e}", f.display()))?;
            b.modules.extend(frag.modules);
            b.statements.extend(frag.statements);
            b.hol_files.extend(frag.hol_files);
            b.correspondences.extend(frag.correspondences);
        }
    }
    let mut seen = HashSet::new();
    for m in &b.modules {
        if !seen.insert(m.module.clone()) {
            return Err(format!(
                "module {} bound twice across bindings files",
                m.module
            ));
        }
    }
    b.statements
        .sort_by(|x, y| (&x.module, &x.decl, &x.sha256).cmp(&(&y.module, &y.decl, &y.sha256)));
    b.statements
        .dedup_by(|x, y| x.module == y.module && x.decl == y.decl && x.sha256 == y.sha256);
    for w in b.statements.windows(2) {
        if w[0].module == w[1].module && w[0].decl == w[1].decl {
            return Err(format!(
                "decl {}.{} bound with two different statement hashes across bindings files",
                w[0].module, w[0].decl
            ));
        }
    }
    b.hol_files
        .sort_by(|x, y| (&x.script, &x.git_blob).cmp(&(&y.script, &y.git_blob)));
    b.hol_files
        .dedup_by(|x, y| x.script == y.script && x.git_blob == y.git_blob);
    for w in b.hol_files.windows(2) {
        if w[0].script == w[1].script {
            return Err(format!(
                "HOL script {} bound twice with different blobs",
                w[0].script
            ));
        }
    }
    b.correspondences.sort_by(|x, y| {
        (
            &x.entry,
            &x.steele_sha256,
            &x.statements_sha256,
            &x.prose_sha256,
        )
            .cmp(&(
                &y.entry,
                &y.steele_sha256,
                &y.statements_sha256,
                &y.prose_sha256,
            ))
    });
    b.correspondences.dedup_by(|x, y| {
        x.entry == y.entry
            && x.steele_sha256 == y.steele_sha256
            && x.statements_sha256 == y.statements_sha256
            && x.prose_sha256 == y.prose_sha256
    });
    for w in b.correspondences.windows(2) {
        if w[0].entry == w[1].entry {
            return Err(format!(
                "entry {} carries two different correspondence triples across bindings files",
                w[0].entry
            ));
        }
    }
    Ok(b)
}

/// Assemble the bibliography: book/refs.tex plus book/refs.d/*.tex
/// (sorted by filename), each fragment spliced immediately before
/// refs.tex's `\end{thebibliography}` — so a batch of new literature
/// citations is a fragment file, never an edit to the shared list.
/// Duplicate \bibitem{key}s across the union are a loud error.
pub fn assemble_refs(book_dir: &Path) -> Result<String, String> {
    let base = std::fs::read_to_string(book_dir.join("refs.tex")).unwrap_or_default();
    let d = book_dir.join("refs.d");
    let mut extra = String::new();
    if d.is_dir() {
        let mut frags: Vec<PathBuf> = std::fs::read_dir(&d)
            .map_err(|e| format!("read {}: {e}", d.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map(|x| x == "tex").unwrap_or(false))
            .collect();
        frags.sort();
        for f in frags {
            let raw = std::fs::read_to_string(&f)
                .map_err(|e| format!("cannot read {}: {e}", f.display()))?;
            extra.push_str(raw.trim_end());
            extra.push('\n');
        }
    }
    const END: &str = "\\end{thebibliography}";
    let out = if extra.is_empty() {
        base
    } else {
        let Some(p) = base.find(END) else {
            return Err(format!(
                "refs.d/ has fragments but refs.tex carries no {END} to splice before"
            ));
        };
        format!("{}{}\n{}", &base[..p], extra.trim_end(), &base[p..])
    };
    // duplicate \bibitem keys across the union are a defect
    let mut keys = HashSet::new();
    for (i, _) in out.match_indices("\\bibitem{") {
        let rest = &out[i + "\\bibitem{".len()..];
        let key = rest.split('}').next().unwrap_or_default();
        if !keys.insert(key.to_string()) {
            return Err(format!(
                "duplicate \\bibitem{{{key}}} across refs.tex + refs.d/ fragments"
            ));
        }
    }
    Ok(out)
}

/// Canonical section order: (page index in meta.pages, row index within
/// that page). Order is a pure function of the rosters — the curated
/// catalogue order — never data a parallel author negotiates in a shared
/// file. Applied to the merged rule set before selection or render.
pub fn canonical_rule_order(
    bf: &mut BookFile,
    pages: &BTreeMap<String, RulesFile>,
) -> Result<(), String> {
    let page_pos: HashMap<&str, usize> = bf
        .meta
        .pages
        .iter()
        .enumerate()
        .map(|(i, p)| (p.as_str(), i))
        .collect();
    let mut key: HashMap<String, (usize, usize)> = HashMap::new();
    for r in &bf.rules {
        let pi = *page_pos
            .get(r.source.as_str())
            .ok_or_else(|| format!("rule {}: source page {} not in meta.pages", r.id, r.source))?;
        let page = pages
            .get(&r.source)
            .ok_or_else(|| format!("rule {}: page {} not loaded", r.id, r.source))?;
        let ri = page
            .rules
            .iter()
            .position(|x| x.name == r.row)
            .ok_or_else(|| format!("rule {}: row '{}' not found in {}", r.id, r.row, r.source))?;
        key.insert(r.id.clone(), (pi, ri));
    }
    bf.rules.sort_by_key(|r| key[&r.id]);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn render_rule(
    ctx: &BookCtx,
    br: &BookRule,
    idx: usize,
    pages: &BTreeMap<String, RulesFile>,
    bindings: &Bindings,
    receipts: &[ReceiptInfo],
    meta: &BookMeta,
    api: &crate::api::ApiCtx,
) -> Result<RuleRender, String> {
    let page = pages.get(&br.source).ok_or_else(|| {
        format!(
            "rule {}: source page {} not in meta.pages",
            br.id, br.source
        )
    })?;
    let row = page
        .rules
        .iter()
        .find(|r| r.name == br.row)
        .ok_or_else(|| {
            format!(
                "rule {}: row '{}' not found in {}",
                br.id, br.row, br.source
            )
        })?;
    if row.amended.trim().is_empty() {
        return Err(format!(
            "rule {}: row '{}' in {} has an empty amended cell — the Steele \
             statement is authored in the rules page first (the book joins it, \
             never duplicates it)",
            br.id, br.row, br.source
        ));
    }

    let tier_head = if row.discipline {
        "edge discipline (glue)".to_string()
    } else {
        match (row.tier, br.alias_target.is_empty()) {
            (Some(1), _) => "core rule".to_string(),
            (Some(2), _) => "admissible rule".to_string(),
            (Some(3), false) => format!(
                "alias for \\textcolor{{DiffBlue}}{{\\rulename{{{}}}}}",
                br.alias_target
            ),
            (Some(3), true) => "alias rule".to_string(),
            _ => "(untiered)".to_string(),
        }
    };

    let mut tex = String::new();
    let _ = writeln!(
        tex,
        "\\rulesection{{{n}}}{{{name}}}{{{tier}}}",
        n = idx + 1,
        name = row.name,
        tier = tier_head,
    );
    // anchor for the synopsis parade's \pageref (rule ids are
    // filename-safe by fiat, so they are label-safe too)
    let _ = writeln!(tex, "\\label{{blcatrule-{}}}", br.id);

    // ---- block: the rule, Steele metanotation ----
    let _ = writeln!(tex, "\\ruleblock{{The rule (Steele metanotation)}}");
    let _ = writeln!(
        tex,
        "\\sourcenote{{as realized in the mechanized development; source row: \\texttt{{{}}} --- \\emph{{{}}}. The metanotation statement is typeset by hand for notational quality; its mechanized ground truth is the Lean statement below, extracted from the sources at every build of this book and hash-bound. The rule \\emph{{roster}} is machine-checked (every mechanized rule tag round-trips to exactly one catalogue row); the statement \\emph{{text}} is editorial, checked by eye against the extracted Lean beside it.}}",
        tex_escape_tt(source_display(&br.source)),
        row.name,
    );
    tex.push_str(&row.amended);
    tex.push('\n');
    // The joined row's `note` is internal-register and is deliberately NOT
    // rendered; the book's own commentary + note fields replace it.
    if !br.commentary.is_empty() {
        tex.push_str("\\par\\medskip\n");
        tex.push_str(&br.commentary);
        tex.push('\n');
    }
    if !br.note.is_empty() {
        let _ = writeln!(tex, "\\cataloguenote{{{}}}", br.note);
    }

    // ---- block: API (producer surfaces — TypeScript, then Rust; one
    // per catalogue entry, immediately after the metanotation block) ----
    match api.entries.get(&br.id) {
        Some(e) => crate::api::render_api_block(e, api, &mut tex)
            .map_err(|e2| format!("rule {}: API block: {e2}", br.id))?,
        None => {
            return Err(format!(
                "rule {}: no API fragment (book/api.toml.d/{}.toml) — every catalogue \
                 entry carries an API section; add the fragment (see DESIGN.md)",
                br.id, br.id
            ))
        }
    }

    // ---- block: Lean statements + bound checker definitions ----
    validate_conditional_label(&br.id, br.conditional, &br.conditional_label)?;
    let mut dash = DashRow {
        name: row.name.clone(),
        tier: row.tier,
        conditional: br.conditional,
        conditional_label: br.conditional_label.clone(),
        hol: br.hol.status.clone(),
        hol_receipt: !br.hol.receipt.is_empty(),
        proof: false,
        ..Default::default()
    };
    let mut worst_drift = Drift::Fresh;

    if !br.lean.is_empty() {
        let _ = writeln!(tex, "\\ruleblock{{Lean statement}}");
        dash.lean_bound = true;
    }
    // current statement rows, gathered for the correspondence triple's
    // statement-side digest (same row shape `bind` writes to the shard)
    let mut stmt_rows: Vec<(String, String, String)> = Vec::new();
    for lean in &br.lean {
        let src_path = ctx.crate_root.join(&lean.src);
        let source = std::fs::read_to_string(&src_path)
            .map_err(|e| format!("rule {}: cannot read {}: {e}", br.id, lean.src))?;
        let mb = bindings
            .modules
            .iter()
            .find(|m| m.module == lean.module)
            .ok_or_else(|| {
                format!(
                    "rule {}: module {} has no binding — run qtsl-book bind",
                    br.id, lean.module
                )
            })?;
        let blob_now = git_blob_sha(&src_path)?;
        let module_moved = blob_now != mb.source_git_blob;

        if !lean.intro.is_empty() {
            tex.push_str("\\par\\medskip\n");
            tex.push_str(&lean.intro);
            tex.push('\n');
        }
        let quoted: Vec<(&String, bool)> = lean
            .decls
            .iter()
            .map(|d| (d, false))
            .chain(lean.full_decls.iter().map(|d| (d, true)))
            .collect();
        for (d, full) in quoted {
            let (stmt, drift) = decl_drift(&source, lean, d, full, bindings, module_moved)
                .map_err(|e| format!("rule {} / {}: {e}", br.id, lean.src))?;
            stmt_rows.push((lean.module.clone(), d.clone(), sha256_hex(stmt.as_bytes())));
            if drift_rank(drift) > drift_rank(worst_drift) {
                worst_drift = drift;
            }
            let head = format!(
                "\\declhead{{{}}}{{{}}}{{{}}}",
                tex_escape_tt(&lean.module),
                tex_escape_tt(d),
                match drift {
                    Drift::Fresh => badge(
                        "BadgeGreen",
                        if full {
                            "definition bound"
                        } else {
                            "statement bound"
                        }
                    ),
                    Drift::ModuleMoved => badge("BadgeAmber", "module source moved since bind"),
                    Drift::StatementChanged => badge("BadgeAmber", "STATEMENT CHANGED since bind"),
                }
            );
            tex.push_str(&head);
            tex.push('\n');
            tex.push_str(&tex_verbatim_block("leansrc", &stmt));
        }
    }

    // ---- block: correspondence (Steele display ↔ Lean statements) ----
    // the reviewer-grade interim of the correspondence layer: a
    // hand-written dictionary, certified as a (display, statement-set,
    // prose) hash triple by `bind`, badged amber the moment any side
    // moves. Its machine-checked successor types the soundness statement
    // against the rule-as-data itself; this block is the ratchet tooth
    // that holds until that statement exists for the rule.
    if !br.correspondence.is_empty() && br.lean.is_empty() {
        return Err(format!(
            "rule {}: correspondence prose but no bound Lean statements to \
             certify it against — a dictionary needs both of its sides",
            br.id
        ));
    }
    if !br.lean.is_empty() {
        let _ = writeln!(
            tex,
            "\\ruleblock{{Correspondence (Steele display $\\leftrightarrow$ Lean)}}"
        );
        let steele_now = sha256_hex(row.amended.as_bytes());
        let stmts_now = statements_digest(&stmt_rows);
        let prose_now = sha256_hex(br.correspondence.as_bytes());
        let recorded = bindings.correspondences.iter().find(|c| c.entry == br.id);
        let state = corr_state(
            !br.correspondence.is_empty(),
            recorded,
            &steele_now,
            &stmts_now,
            &prose_now,
        );
        match state {
            CorrState::Absent => {
                dash.corr = 0;
                let _ = writeln!(
                    tex,
                    "\\absentbox{{NO CORRESPONDENCE DICTIONARY YET}}{{no reviewer-certified \
                     dictionary maps the displayed rule onto the mechanized statements above; \
                     until one is written and certified, that mapping rests on this \
                     section\\textquotesingle s editorial care alone.}}"
                );
            }
            _ => {
                let b = match state {
                    CorrState::Certified => {
                        dash.corr = 2;
                        badge(
                            "BadgeGreen",
                            "reviewer-certified against the displayed texts",
                        )
                    }
                    CorrState::Unrecorded => {
                        dash.corr = 1;
                        badge(
                            "BadgeAmber",
                            "dictionary present but UNCERTIFIED --- no recorded triple",
                        )
                    }
                    CorrState::Drifted {
                        steele,
                        statements,
                        prose,
                    } => {
                        dash.corr = 1;
                        let mut what: Vec<&str> = Vec::new();
                        if steele {
                            what.push("the Steele display");
                        }
                        if statements {
                            what.push("a bound Lean statement");
                        }
                        if prose {
                            what.push("the dictionary text");
                        }
                        badge(
                            "BadgeAmber",
                            &format!(
                                "{} CHANGED since certification --- re-review and re-certify",
                                what.join(" and ")
                            ),
                        )
                    }
                    CorrState::Absent => unreachable!(),
                };
                tex.push_str(&b);
                tex.push('\n');
                let _ = writeln!(
                    tex,
                    "\\sourcenote{{The dictionary below is a reviewer-certified statement of \
                     how the mechanized statements above interpret the displayed rule: display \
                     metavariable $\\mapsto$ Lean binder, each display hypothesis $\\mapsto$ \
                     the premise or side condition carrying it, the display conclusion \
                     $\\mapsto$ the goal --- with any deliberate difference in width between \
                     display and mechanization named outright. Certification is recorded as a \
                     hash triple over (the displayed cell, the extracted statement texts, this \
                     dictionary\\textquotesingle s own text); if any of the three changes, this \
                     block turns amber until a reviewer re-certifies. The correspondence claim \
                     itself remains editorial --- reviewer-grade, not machine-checked; its \
                     machine-checked successor types each soundness statement against the rule \
                     as a structured object, and supersedes this block per rule as it ships.}}"
                );
                tex.push_str(&br.correspondence);
                tex.push('\n');
            }
        }
    }

    // ---- block: Lean verifier receipts (one table per bound module) ----
    if !br.lean.is_empty() {
        let _ = writeln!(tex, "\\ruleblock{{Lean verifier receipts}}");
        if ctx.consult_receipts {
            for lean in &br.lean {
                let mb = bindings
                    .modules
                    .iter()
                    .find(|m| m.module == lean.module)
                    .expect("binding checked above");
                let mine: Vec<&ReceiptInfo> = receipts
                    .iter()
                    .filter(|r| r.module == lean.module)
                    .collect();
                if mb.olean_sha256.is_empty() {
                    let _ = writeln!(
                        tex,
                        "\\sourcenote{{module \\texttt{{{}}}; {}. The statements above are hash-bound to the source file, but no build attestation exists for this module yet, so no receipt can be judged to attest the quoted build.}}",
                        tex_escape_tt(&lean.module),
                        tex_escape_text(&mb.olean_provenance),
                    );
                } else {
                    let _ = writeln!(
                        tex,
                        "\\sourcenote{{module \\texttt{{{}}}; bound build \\texttt{{{}\\ldots}} ({}). A receipt is an ed25519-signed attestation of (module, compiled-artifact SHA-256, environment SHA-256, checker layers); the store receipts attesting the bound build are listed, each signature verified at render against the pinned trust roots and its signer shown by key fingerprint. Receipts attesting superseded builds credit no layer and are omitted from this rendering (the count of omissions, if any, is noted below).}}",
                        tex_escape_tt(&lean.module),
                        &mb.olean_sha256[..12],
                        tex_escape_text(&mb.olean_provenance),
                    );
                }
                credit_layers(
                    receipts,
                    &lean.module,
                    &mb.olean_sha256,
                    &mut dash.layer_state,
                );
                // stale receipts are omitted from the rendering (design ruling,
                // 2026-07-20): a receipt attesting a superseded build credits
                // no layer, so listing it is noise — the store keeps it; the
                // rendering counts the omissions instead.
                let n_stale = mine
                    .iter()
                    .filter(|r| mb.olean_sha256.is_empty() || r.olean_sha256 != mb.olean_sha256)
                    .count();
                let current_mine: Vec<&&ReceiptInfo> = mine
                    .iter()
                    .filter(|r| !mb.olean_sha256.is_empty() && r.olean_sha256 == mb.olean_sha256)
                    .collect();
                if mb.olean_sha256.is_empty() {
                    tex.push_str(&badge(
                        "BadgeAmber",
                        "NO ATTESTED BUILD BOUND for this module",
                    ));
                    tex.push('\n');
                }
                if current_mine.is_empty() {
                    if !mb.olean_sha256.is_empty() {
                        tex.push_str(&badge(
                            "BadgeAmber",
                            "NO CURRENT RECEIPT attests the bound build",
                        ));
                        tex.push('\n');
                    }
                    if n_stale > 0 {
                        let _ = writeln!(
                            tex,
                            "\\sourcenote{{{n_stale} receipt(s) in the store attest superseded builds of this module and are omitted from this rendering.}}"
                        );
                    }
                    continue;
                }
                let _ = writeln!(tex, "\\begin{{receipttable}}");
                for r in &current_mine {
                    let b = badge("BadgeGreen", "current");
                    // signature status: "valid, pinned root" (green) or the
                    // failure text in full (red — an outright rejection).
                    let trust = if r.trust.contains("TRUSTED") {
                        "\\trustok{valid, pinned root}".to_string()
                    } else {
                        format!("\\trustbad{{{}}}", tex_escape_text(&r.trust))
                    };
                    let signer_fp = if r.signer.len() >= 16 {
                        format!("{}\\ldots", &r.signer[..16])
                    } else {
                        r.signer.clone()
                    };
                    let _ = writeln!(
                        tex,
                        "\\receiptrow{{{sig}}}{{{signer}}}{{{ts}}}{{{layers}}}{{{trust}}}{{{b}}}",
                        sig = tex_escape_tt(&r.sig16),
                        signer = tex_escape_tt(&signer_fp),
                        ts = tex_escape_text(&r.ts),
                        layers = tex_escape_tt(&r.layers.join("+")),
                    );
                }
                let _ = writeln!(tex, "\\end{{receipttable}}");
                if n_stale > 0 {
                    let _ = writeln!(
                        tex,
                        "\\sourcenote{{{n_stale} further receipt(s) in the store attest superseded builds of this module and are omitted from this rendering.}}"
                    );
                }
            }
            // per-layer coverage line (aggregated over the rule's modules)
            let mut cov = String::from("\\layerline{");
            for (i, (l, gloss)) in GATE_LAYERS.iter().enumerate() {
                let state = match dash.layer_state[i] {
                    2 => badge("BadgeGreen", "current"),
                    1 => badge("BadgeAmber", "stale only"),
                    _ => badge("BadgeGray", "none"),
                };
                let _ = write!(cov, "\\layeritem{{{l}}}{{{gloss}}}{{{state}}}");
            }
            cov.push('}');
            tex.push_str(&cov);
            tex.push('\n');
            // comparator line
            let comp = if br.comparator.is_empty() {
                format!(
                    "{} no fixture in the three-implementation comparator harness (compiled / kernel-interpreted / reference-interpreted) exercises this rule.",
                    badge("BadgeGray", "comparator: none")
                )
            } else {
                br.comparator.clone()
            };
            let _ = writeln!(tex, "\\sourcenote{{{comp}}}");
        } else {
            tex.push_str(&badge(
                "BadgeAmber",
                "receipt store NOT consulted this render (--no-receipts)",
            ));
            tex.push('\n');
        }
    }

    // ---- block: HOL statement ----
    let _ = writeln!(tex, "\\ruleblock{{HOL4 statement}}");
    match br.hol.status.as_str() {
        "ported" => {
            let src_path = ctx.crate_root.join(&br.hol.script);
            let source = std::fs::read_to_string(&src_path)
                .map_err(|e| format!("rule {}: cannot read {}: {e}", br.id, br.hol.script))?;
            let hb = bindings
                .hol_files
                .iter()
                .find(|h| h.script == br.hol.script);
            let hol_moved = match hb {
                Some(h) => git_blob_sha(&src_path)? != h.git_blob,
                None => true,
            };
            // display the script by file name only — the book's paths are
            // repo-layout-neutral (export-sanitization posture).
            let script_display = Path::new(&br.hol.script)
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| br.hol.script.clone());
            let _ = writeln!(
                tex,
                "\\sourcenote{{theory \\texttt{{{}}}, HOL4 development script \\texttt{{{}}} {}}}",
                tex_escape_tt(&br.hol.theory),
                tex_escape_tt(&script_display),
                if hol_moved {
                    badge("BadgeAmber", "script moved since bind")
                } else {
                    badge("BadgeGreen", "script bound")
                }
            );
            for d in &br.hol.decls {
                let block = extract_hol_decl(&source, d)
                    .map_err(|e| format!("rule {} / {}: {e}", br.id, br.hol.script))?;
                let _ = writeln!(tex, "\\holhead{{{}}}", tex_escape_tt(d));
                tex.push_str(&tex_verbatim_block("holsrc", &block));
            }
        }
        _ => {
            let _ = writeln!(
                tex,
                "\\absentbox{{{}}}{{{}}}",
                if br.hol.status == "out-of-scope" {
                    "OUT OF SCOPE BY DESIGN"
                } else {
                    "NO HOL STATEMENT YET"
                },
                br.hol.reason
            );
        }
    }

    // ---- block: HOL verifier receipts ----
    let _ = writeln!(tex, "\\ruleblock{{HOL verifier receipts}}");
    if br.hol.receipt.is_empty() {
        let _ = writeln!(
            tex,
            "\\absentbox{{NONE}}{{no HOL verification receipt exists for this rule.}}"
        );
    } else {
        let _ = writeln!(
            tex,
            "{} {}",
            badge("BadgeBlue", "documentary"),
            br.hol.receipt
        );
        let _ = writeln!(tex, "\\sourcenote{{{}}}", meta.hol_store_note);
    }

    // ---- block: the proof ----
    let _ = writeln!(tex, "\\ruleblock{{Proof}}");
    let proof_path = ctx.crate_root.join(&br.proof);
    let proof = std::fs::read_to_string(&proof_path)
        .map_err(|e| format!("rule {}: cannot read proof {}: {e}", br.id, br.proof))?;
    dash.proof = true;
    match worst_drift {
        Drift::StatementChanged => {
            let _ = writeln!(
                tex,
                "{}",
                badge(
                    "BadgeAmber",
                    "a quoted statement CHANGED since this proof was written --- testimony, not warrant, until re-reviewed"
                )
            );
        }
        Drift::ModuleMoved => {
            let _ = writeln!(
                tex,
                "{}",
                badge(
                    "BadgeAmber",
                    "module source moved since bind; statements intact"
                )
            );
        }
        Drift::Fresh => {}
    }
    dash.drift = rule_dash_drift(!br.lean.is_empty(), worst_drift);
    tex.push_str(&proof);
    tex.push('\n');

    Ok(RuleRender {
        id: br.id.clone(),
        tex,
        dash,
    })
}

/// Dashboard drift for a full rule section: `None` (renders \dnone —
/// absent) when the rule cites no Lean at all; otherwise the worst drift
/// across its cited decls. The fold's accumulator starts at `Fresh`, so
/// stamping it unconditionally would award a green \dok to an empty Lean
/// column (caught by the census pass, 2026-07-20: 14 honest-absence
/// rules wore green on the dashboard while carrying no Lean statement).
pub fn rule_dash_drift(cites_lean: bool, worst: Drift) -> Option<Drift> {
    if cites_lean {
        Some(worst)
    } else {
        None
    }
}

fn drift_rank(d: Drift) -> u8 {
    match d {
        Drift::Fresh => 0,
        Drift::ModuleMoved => 1,
        Drift::StatementChanged => 2,
    }
}

// ============================ dashboard ============================

/// One synopsis-parade entry (the emit-fragment's opening section,
/// design ruling, 2026-07-20): the rule's Steele form left-aligned, its
/// SmallCaps name at the right, then a dotted leader to the page number
/// of the full entry. A simple single-`\inferrule` mathpar cell is
/// re-typeset via `\paradeentry` (label option stripped — the parade
/// places the name itself, so the leader shares its baseline); anything
/// else (prose-form rules, bare displays, multi-rule cells) rides the
/// `\paradeblock` fallback: content as authored, name + leader on the
/// line below.
pub fn parade_entry(amended: &str, name: &str, label: &str) -> String {
    let t = amended.trim();
    if let Some(inner) = t
        .strip_prefix("\\begin{mathpar}")
        .and_then(|s| s.strip_suffix("\\end{mathpar}"))
    {
        let inner = inner.trim();
        if inner.matches("\\inferrule").count() == 1 && !inner.contains("\\and") {
            let stripped = strip_inferrule_option(inner);
            return format!("\\paradeentry{{{stripped}}}{{{name}}}{{{label}}}\n");
        }
    }
    format!("\\paradeblock{{{t}}}{{{name}}}{{{label}}}\n")
}

/// Drop the `[...]` option (e.g. `[Right=\rulename{X}]`) after
/// `\inferrule` / `\inferrule*`. Option bodies in the catalogue carry no
/// nested brackets, so the first `]` closes it.
fn strip_inferrule_option(inner: &str) -> String {
    let star = inner.find("\\inferrule*").map(|i| i + "\\inferrule*".len());
    let plain = star.or_else(|| inner.find("\\inferrule").map(|i| i + "\\inferrule".len()));
    if let Some(after) = plain {
        let rest = &inner[after..];
        let rest_trim = rest.trim_start();
        if let Some(opt) = rest_trim.strip_prefix('[') {
            if let Some(close) = opt.find(']') {
                return format!("{}{}", &inner[..after], &opt[close + 1..]);
            }
        }
    }
    inner.to_string()
}

pub fn render_dashboard(
    pages: &BTreeMap<String, RulesFile>,
    page_order: &[String],
    covered: &HashMap<String, DashRow>,
    intro: &str,
) -> String {
    let mut tex = String::new();
    let _ = writeln!(tex, "\\dashboardhead{{{intro}}}");
    // Rows are collected, then stably sorted by tier class ascending —
    // core < adm < alias < glue — with roster order (page index, row
    // index) preserved within a class. The former per-page \dashpage
    // group headers do not survive the interleaving; each row instead
    // carries a small source mark after its name (\dashsrc), keyed to
    // the catalogue page the row joins from.
    let mut rows: Vec<(u8, String)> = Vec::new();
    for p in page_order {
        let Some(rf) = pages.get(p) else { continue };
        let src_mark = page_source_mark(p);
        for r in &rf.rules {
            if r.tier.is_none() && !r.discipline {
                continue; // not a proof rule (the sp-axiom)
            }
            // the glue category (edge discipline) stays visible, counted
            // apart from the three tiers (TowerCitation rendering note).
            let (tier, class_rank) = if r.discipline {
                ("glue", 4u8)
            } else {
                // bare class labels — the 1/2/3 numerals were nixed
                // (design ruling, 2026-07-20)
                match r.tier {
                    Some(1) => ("core", 1),
                    Some(2) => ("adm.", 2),
                    Some(3) => ("alias", 3),
                    _ => ("", 5),
                }
            };
            let key = format!("{}::{}", p, r.name);
            let row = covered.get(&key);
            let (lean, corr, layers, hol, proof) = match row {
                Some(d) => {
                    // conditional marks carry their named-profile label as
                    // the macro's optional argument (\dcond[DTMC]); empty
                    // label = the macros' generic "hyp" default.
                    let cond_mark = |base: &str| {
                        if d.conditional_label.is_empty() {
                            base.to_string()
                        } else {
                            format!("{base}[{}]", d.conditional_label)
                        }
                    };
                    let lean = match (d.drift, d.conditional) {
                        (Some(Drift::Fresh), false) => "\\dok".to_string(),
                        (Some(Drift::Fresh), true) => cond_mark("\\dcond"),
                        // amber carries the conditional-warrant flag too: an
                        // unconditional \damber masked `conditional = true`
                        // (M2 instrument note, 2026-07-20 — the census's cond
                        // count read 12 while ground truth was 15, the three
                        // hidden ones all module-moved rows). the label rides
                        // along — flag and label survive staleness alike.
                        (Some(Drift::ModuleMoved), false) => "\\damber".to_string(),
                        (Some(Drift::ModuleMoved), true) => cond_mark("\\dambercond"),
                        (Some(Drift::StatementChanged), _) => "\\dchanged".to_string(),
                        (None, _) => "\\dnone".to_string(),
                    };
                    let corr = match d.corr {
                        2 => "\\dok",
                        1 => "\\damber",
                        _ => "\\dnone",
                    }
                    .to_string();
                    let mut ls = String::new();
                    for (i, (l, _)) in GATE_LAYERS.iter().enumerate() {
                        let g = match d.layer_state[i] {
                            2 => "\\lcur",
                            1 => "\\lstale",
                            _ => "\\lnone",
                        };
                        let _ = write!(ls, "{g}{{{}}}", &l[..1]);
                    }
                    let hol = match d.hol.as_str() {
                        "ported" => "\\dok",
                        "out-of-scope" => "\\dscope",
                        _ => "\\dnone",
                    };
                    (
                        lean,
                        corr,
                        ls,
                        hol.to_string(),
                        if d.proof { "\\dok" } else { "\\dnone" }.to_string(),
                    )
                }
                None => (
                    "\\dnone".to_string(),
                    "\\dnone".to_string(),
                    {
                        let mut ls = String::new();
                        for (l, _) in GATE_LAYERS.iter() {
                            let _ = write!(ls, "\\lnone{{{}}}", &l[..1]);
                        }
                        ls
                    },
                    "\\dnone".to_string(),
                    "\\dnone".to_string(),
                ),
            };
            let holr = match row {
                Some(d) if d.hol_receipt => "\\ddoc",
                _ => "\\dnone",
            };
            // Isabelle column: uniformly absent — there is no in-house
            // Isabelle development to date (see the dashboard caption).
            rows.push((
                class_rank,
                format!(
                    "\\dashrow{{{name}~\\dashsrc{{{src}}}}}{{{tier}}}{{{lean}}}{{{corr}}}{{{layers}}}{{{hol}}}{{{holr}}}{{\\dnone}}{{{proof}}}\n",
                    name = r.name,
                    src = src_mark,
                ),
            ));
        }
    }
    rows.sort_by_key(|(rank, _)| *rank); // stable: roster order kept in-class
    for (_, line) in rows {
        tex.push_str(&line);
    }
    let _ = writeln!(tex, "\\dashboardfoot");
    tex
}

/// Short source mark for a dashboard row: which catalogue page the row
/// joins from, compressed to a stable label a cold reader can key to the
/// caption (BL = the Bernstein Logic rules page — composition rules
/// included, since the former AG page folded into it; QTSL = the QTSL
/// rule roster). Unknown pages fall back to their stem.
fn page_source_mark(p: &str) -> String {
    let stem = source_display(p).trim_end_matches(".toml");
    match stem {
        "rules" | "BL-rules" => "BL".to_string(),
        "QTSL-rules" => "QTSL".to_string(),
        other => tex_escape_tt(other),
    }
}

// ============================ escapes ============================

/// Display form of a rules-source path: file name only. The book's paths
/// are repo-layout-neutral (export-sanitization posture — kin to the HOL
/// script display in `render_rule`), and the config's relative segments
/// (`../`) are build machinery, not reader-facing content. Also used for
/// the emit-mode section grouping, whose prefix tests match the file
/// *name* (`AG-…`, `QTSL-…`), never the path.
pub fn source_display(s: &str) -> &str {
    s.rsplit('/').next().unwrap_or(s)
}

fn tex_escape_tt(s: &str) -> String {
    s.replace('\\', "\\textbackslash{}")
        .replace('_', "\\_")
        .replace('#', "\\#")
        .replace('%', "\\%")
        .replace('&', "\\&")
}

fn tex_escape_path(s: &str) -> String {
    format!("\\texttt{{{}}}", tex_escape_tt(s))
}

fn tex_escape_text(s: &str) -> String {
    s.replace('\\', "\\textbackslash{}")
        .replace('_', "\\_")
        .replace('#', "\\#")
        .replace('%', "\\%")
        .replace('&', "\\&")
        .replace('\'', "\\textquotesingle{}")
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEAN_SAMPLE: &str = r#"
/-- doc line one
and two. -/
theorem sound_foo {H : Hypernet} (st : Step H)
    (h : Valid) :
    st.seq.semanticallyValid H := by
  exact trivial

structure StepData (H : Hypernet) where
  seq : Sequent
  valid : True

def toBar (st : Step H) : Bar H where
  seq := st.seq

theorem term_mode {x : Nat} :
    x = x :=
  rfl
"#;

    #[test]
    fn extracts_theorem_with_doc_and_cuts_proof() {
        let s = extract_lean_decl(LEAN_SAMPLE, "sound_foo").unwrap();
        assert!(s.starts_with("/-- doc line one"));
        assert!(s.contains("semanticallyValid H"));
        assert!(!s.contains(":= by"));
        assert!(!s.contains("exact trivial"));
    }

    #[test]
    fn extracts_structure_with_fields() {
        let s = extract_lean_decl(LEAN_SAMPLE, "StepData").unwrap();
        assert!(s.contains("where"));
        assert!(s.contains("valid : True"));
        assert!(!s.contains("def toBar"));
    }

    #[test]
    fn extracts_def_signature_up_to_where() {
        let s = extract_lean_decl(LEAN_SAMPLE, "toBar").unwrap();
        assert!(s.contains(": Bar H"));
        assert!(!s.contains("seq := st.seq"));
    }

    #[test]
    fn extracts_term_mode_theorem() {
        let s = extract_lean_decl(LEAN_SAMPLE, "term_mode").unwrap();
        assert!(s.contains("x = x"));
        assert!(!s.contains("rfl"));
    }

    #[test]
    fn decl_name_prefix_no_false_match() {
        // "toBar" must not match "toBarometer"
        let src = "def toBarometer : Nat := 3\ndef toBar : Nat := 4\n";
        let s = extract_lean_decl(src, "toBar").unwrap();
        assert!(s.contains("toBar :"));
        assert!(!s.contains("toBarometer"));
    }

    const HOL_SAMPLE: &str = r#"
Definition fooCheck_def:
  fooCheck x = (x = 0)
End

Theorem foo_sound:
  !x. fooCheck x ==> P x
Proof
  rw[]
QED
"#;

    #[test]
    fn full_mode_keeps_def_body_and_stops_at_next_toplevel() {
        let src = "\
/-- the check. -/
def fooCheck (x : Nat) : Bool :=
  match x with
  | 0 => true
  | _ => false

def other : Nat := 3
";
        let s = extract_lean_decl_full(src, "fooCheck").unwrap();
        assert!(s.starts_with("/-- the check. -/"));
        assert!(s.contains("| 0 => true"));
        assert!(!s.contains("def other"));
        // and signature mode still cuts the same decl at `:=`
        let sig = extract_lean_decl(src, "fooCheck").unwrap();
        assert!(!sig.contains("match"));
    }

    #[test]
    fn extracts_dotted_decl_name() {
        // qtsl-aux pattern: `theorem Supermartingale.exists_ae_tendsto_of_nonneg`
        let src = "theorem Supermartingale.exists_ae_tendsto_of_nonneg {f : X}\n    (hf : P f) :\n    Q f := by\n  exact trivial\n";
        let s = extract_lean_decl(src, "Supermartingale.exists_ae_tendsto_of_nonneg").unwrap();
        assert!(s.contains("Q f"));
        assert!(!s.contains("trivial"));
    }

    #[test]
    fn extracts_hol_definition_through_end() {
        let s = extract_hol_decl(HOL_SAMPLE, "Definition fooCheck_def").unwrap();
        assert!(s.starts_with("Definition fooCheck_def:"));
        assert!(s.trim_end().ends_with("End"));
    }

    #[test]
    fn extracts_hol_theorem_statement_only() {
        let s = extract_hol_decl(HOL_SAMPLE, "Theorem foo_sound").unwrap();
        assert!(s.contains("fooCheck x ==> P x"));
        assert!(!s.contains("Proof"));
        assert!(!s.contains("QED"));
    }

    // ==================== fragment loading ====================

    fn tdir(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("blbook-{}-{}", name, std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(d.join("book.toml.d")).unwrap();
        std::fs::create_dir_all(d.join("bindings.toml.d")).unwrap();
        d
    }

    const META_ONLY: &str = r#"
[meta]
title = "t"
subtitle = "s"
preface = "p"
dashboard_intro = "d"
hol_store_note = "h"
pages = ["rules.toml", "second.toml"]
"#;

    fn frag_rule(id: &str, source: &str, row: &str) -> String {
        format!(
            "[[rule]]\nid = \"{id}\"\nsource = \"{source}\"\nrow = \"{row}\"\nproof = \"book/proofs/{id}.tex\"\n[rule.hol]\nstatus = \"absent\"\n"
        )
    }

    #[test]
    fn fragments_merge_with_book_toml() {
        let d = tdir("merge");
        std::fs::write(d.join("book.toml"), META_ONLY).unwrap();
        std::fs::write(
            d.join("book.toml.d/Foo.toml"),
            frag_rule("Foo", "rules.toml", "Foo"),
        )
        .unwrap();
        std::fs::write(
            d.join("book.toml.d/Bar_cov.toml"),
            "[[coverage]]\nsource = \"rules.toml\"\nrow = \"Bar/cov\"\n[[coverage.lean]]\nmodule = \"M\"\nsrc = \"x.lean\"\ndecls = [\"y\"]\n",
        )
        .unwrap();
        let (bf, _) = load_book_dir(&d).unwrap();
        assert_eq!(bf.rules.len(), 1);
        assert_eq!(bf.rules[0].id, "Foo");
        assert_eq!(bf.coverage.len(), 1);
        assert_eq!(bf.coverage[0].row, "Bar/cov"); // stem = sanitized row
    }

    #[test]
    fn fragment_stem_must_match_id() {
        let d = tdir("stem");
        std::fs::write(d.join("book.toml"), META_ONLY).unwrap();
        std::fs::write(
            d.join("book.toml.d/Wrong.toml"),
            frag_rule("Foo", "rules.toml", "Foo"),
        )
        .unwrap();
        let e = load_book_dir(&d).unwrap_err();
        assert!(e.contains("file stem"), "{e}");
    }

    #[test]
    fn duplicate_rule_id_across_files_is_loud() {
        let d = tdir("dupid");
        let mut book = META_ONLY.to_string();
        book.push_str(&frag_rule("Foo", "rules.toml", "FooRow"));
        std::fs::write(d.join("book.toml"), book).unwrap();
        std::fs::write(
            d.join("book.toml.d/Foo.toml"),
            frag_rule("Foo", "rules.toml", "Other"),
        )
        .unwrap();
        let e = load_book_dir(&d).unwrap_err();
        assert!(e.contains("duplicate rule id"), "{e}");
    }

    #[test]
    fn duplicate_row_claim_rule_vs_coverage_is_loud() {
        let d = tdir("duprow");
        let mut book = META_ONLY.to_string();
        book.push_str("[[coverage]]\nsource = \"rules.toml\"\nrow = \"Foo\"\n[[coverage.lean]]\nmodule = \"M\"\nsrc = \"x.lean\"\n");
        std::fs::write(d.join("book.toml"), book).unwrap();
        std::fs::write(
            d.join("book.toml.d/FooR.toml"),
            frag_rule("FooR", "rules.toml", "Foo"),
        )
        .unwrap();
        let e = load_book_dir(&d).unwrap_err();
        assert!(e.contains("claimed twice"), "{e}");
    }

    #[test]
    fn fragment_carries_exactly_one_entry() {
        let d = tdir("two");
        std::fs::write(d.join("book.toml"), META_ONLY).unwrap();
        let two = format!(
            "{}{}",
            frag_rule("A", "rules.toml", "A"),
            frag_rule("B", "rules.toml", "B")
        );
        std::fs::write(d.join("book.toml.d/A.toml"), two).unwrap();
        let e = load_book_dir(&d).unwrap_err();
        assert!(e.contains("exactly one"), "{e}");
    }

    #[test]
    fn bindings_fragments_merge_dedup_and_conflict() {
        let d = tdir("bind");
        std::fs::write(d.join("book.toml"), META_ONLY).unwrap();
        std::fs::write(
            d.join("bindings.toml"),
            "[[statement]]\nmodule = \"M\"\ndecl = \"x\"\nsha256 = \"aa\"\n",
        )
        .unwrap();
        // exact duplicate in a fragment: collapses
        std::fs::write(
            d.join("bindings.toml.d/E1.toml"),
            "[[statement]]\nmodule = \"M\"\ndecl = \"x\"\nsha256 = \"aa\"\n[[statement]]\nmodule = \"M\"\ndecl = \"y\"\nsha256 = \"bb\"\n",
        )
        .unwrap();
        let (_, b) = load_book_dir(&d).unwrap();
        assert_eq!(b.statements.len(), 2);
        // conflicting hash for the same (module, decl): loud
        std::fs::write(
            d.join("bindings.toml.d/E2.toml"),
            "[[statement]]\nmodule = \"M\"\ndecl = \"x\"\nsha256 = \"cc\"\n",
        )
        .unwrap();
        let e = load_book_dir(&d).unwrap_err();
        assert!(e.contains("two different statement hashes"), "{e}");
    }

    #[test]
    fn canonical_order_follows_roster_not_filenames() {
        let d = tdir("order");
        std::fs::write(d.join("book.toml"), META_ONLY).unwrap();
        // alphabetical fragment order: Alpha < Beta < Gamma; roster order
        // inverts it across two pages.
        std::fs::write(
            d.join("book.toml.d/Alpha.toml"),
            frag_rule("Alpha", "second.toml", "A"),
        )
        .unwrap();
        std::fs::write(
            d.join("book.toml.d/Beta.toml"),
            frag_rule("Beta", "rules.toml", "B"),
        )
        .unwrap();
        std::fs::write(
            d.join("book.toml.d/Gamma.toml"),
            frag_rule("Gamma", "rules.toml", "G"),
        )
        .unwrap();
        let (mut bf, _) = load_book_dir(&d).unwrap();
        let page = |names: &[&str]| -> RulesFile {
            let rules = names
                .iter()
                .map(|n| {
                    format!(
                        "[[rule]]\nname = \"{n}\"\nstratum = \"\"\noriginal = \"\"\namended = \"x\"\n"
                    )
                })
                .collect::<String>();
            toml::from_str(&format!(
                "[meta]\ntitle = \"t\"\nsubtitle = \"s\"\nlegend = \"l\"\ncolophon = \"c\"\n{rules}"
            ))
            .unwrap()
        };
        let mut pages = BTreeMap::new();
        pages.insert("rules.toml".to_string(), page(&["G", "B"]));
        pages.insert("second.toml".to_string(), page(&["A"]));
        canonical_rule_order(&mut bf, &pages).unwrap();
        let got: Vec<&str> = bf.rules.iter().map(|r| r.id.as_str()).collect();
        // rules.toml first (G before B per roster), then second.toml's A
        assert_eq!(got, vec!["Gamma", "Beta", "Alpha"]);
    }

    #[test]
    fn refs_fragments_splice_before_end_and_dup_keys_are_loud() {
        let d = tdir("refs");
        std::fs::create_dir_all(d.join("refs.d")).unwrap();
        std::fs::write(
            d.join("refs.tex"),
            "\\begin{thebibliography}{99}\n\\bibitem{a}\nA.\n\\end{thebibliography}\n",
        )
        .unwrap();
        std::fs::write(d.join("refs.d/b1.tex"), "\\bibitem{b}\nB.\n").unwrap();
        let out = assemble_refs(&d).unwrap();
        let pb = out.find("\\bibitem{b}").unwrap();
        let pe = out.find("\\end{thebibliography}").unwrap();
        assert!(pb < pe, "fragment must land inside the bibliography");
        // duplicate key across base + fragment: loud
        std::fs::write(d.join("refs.d/b2.tex"), "\\bibitem{a}\ndup.\n").unwrap();
        let e = assemble_refs(&d).unwrap_err();
        assert!(e.contains("duplicate \\bibitem{a}"), "{e}");
    }

    #[test]
    fn no_lean_rule_dashboards_absent_not_fresh() {
        // the stamping decision (census catch, 2026-07-20)
        assert_eq!(rule_dash_drift(false, Drift::Fresh), None);
        assert_eq!(rule_dash_drift(false, Drift::StatementChanged), None);
        assert_eq!(rule_dash_drift(true, Drift::Fresh), Some(Drift::Fresh));
        assert_eq!(
            rule_dash_drift(true, Drift::ModuleMoved),
            Some(Drift::ModuleMoved)
        );
    }

    #[test]
    fn dashboard_none_drift_renders_dnone_even_with_proof() {
        // glyph half of the pair: a row with drift=None (no Lean cited)
        // must show \dnone in the Lean column even when its proof exists.
        let mut pages: BTreeMap<String, RulesFile> = BTreeMap::new();
        let rf: RulesFile = toml::from_str(
            r#"
            [meta]
            title = "t"
            subtitle = "s"
            legend = "l"
            colophon = "c"
            [[rule]]
            name = "NoLean"
            stratum = "s"
            tier = 3
            original = "o"
            amended = "a"
            "#,
        )
        .unwrap();
        pages.insert("p.toml".to_string(), rf);
        let mut covered: HashMap<String, DashRow> = HashMap::new();
        covered.insert(
            "p.toml::NoLean".to_string(),
            DashRow {
                name: "NoLean".to_string(),
                tier: Some(3),
                drift: None,
                proof: true,
                hol: "out-of-scope".to_string(),
                ..Default::default()
            },
        );
        let tex = render_dashboard(&pages, &["p.toml".to_string()], &covered, "i");
        let row = tex
            .lines()
            .find(|l| l.starts_with("\\dashrow{NoLean"))
            .expect("row rendered");
        // Lean column (3rd argument) exactly \dnone, then the corr column
        // (also \dnone here); the proof column's \dok is earned
        // (proof = true) and deliberately not forbidden.
        assert!(
            row.starts_with("\\dashrow{NoLean~\\dashsrc{p}}{alias}{\\dnone}{\\dnone}{\\lnone{b}"),
            "Lean and corr columns must be \\dnone for a no-Lean rule: {row}"
        );
    }

    /// Regression pair for the amber/conditional composition (M2 instrument
    /// note, 2026-07-20): a module-moved row with `conditional = true` must
    /// render \dambercond — the plain \damber previously swallowed the flag.
    fn amber_row(conditional: bool) -> String {
        amber_row_labeled(conditional, "")
    }

    fn amber_row_labeled(conditional: bool, label: &str) -> String {
        let mut pages: BTreeMap<String, RulesFile> = BTreeMap::new();
        let rf: RulesFile = toml::from_str(
            r#"
            [meta]
            title = "t"
            subtitle = "s"
            legend = "l"
            colophon = "c"
            [[rule]]
            name = "Moved"
            stratum = "s"
            tier = 2
            original = "o"
            amended = "a"
            "#,
        )
        .unwrap();
        pages.insert("p.toml".to_string(), rf);
        let mut covered: HashMap<String, DashRow> = HashMap::new();
        covered.insert(
            "p.toml::Moved".to_string(),
            DashRow {
                name: "Moved".to_string(),
                tier: Some(2),
                drift: Some(Drift::ModuleMoved),
                conditional,
                conditional_label: label.to_string(),
                proof: true,
                hol: "absent".to_string(),
                ..Default::default()
            },
        );
        let tex = render_dashboard(&pages, &["p.toml".to_string()], &covered, "i");
        tex.lines()
            .find(|l| l.starts_with("\\dashrow{Moved"))
            .expect("row rendered")
            .to_string()
    }

    #[test]
    fn dashboard_amber_conditional_renders_dambercond() {
        let row = amber_row(true);
        assert!(
            row.starts_with("\\dashrow{Moved~\\dashsrc{p}}{adm.}{\\dambercond}"),
            "amber row must carry the conditional flag: {row}"
        );
    }

    #[test]
    fn dashboard_amber_unconditional_renders_damber() {
        let row = amber_row(false);
        assert!(
            row.starts_with("\\dashrow{Moved~\\dashsrc{p}}{adm.}{\\damber}"),
            "unconditional amber row must stay plain \\damber: {row}"
        );
    }

    /// The named-profile superscript: a conditional
    /// row whose warrant is a single crisp profile name renders the name
    /// as the mark's optional argument — and the label survives staleness
    /// exactly as the flag does.
    #[test]
    fn dashboard_conditional_label_rides_the_mark() {
        let row = amber_row_labeled(true, "DTMC");
        assert!(
            row.starts_with("\\dashrow{Moved~\\dashsrc{p}}{adm.}{\\dambercond[DTMC]}"),
            "labeled conditional row must render \\dambercond[DTMC]: {row}"
        );
    }

    #[test]
    fn conditional_label_requires_the_flag() {
        assert!(validate_conditional_label("R", true, "DTMC").is_ok());
        assert!(validate_conditional_label("R", false, "").is_ok());
        assert!(validate_conditional_label("R", false, "DTMC").is_err());
        assert!(validate_conditional_label("R", true, "bad]label").is_err());
        assert!(validate_conditional_label("R", true, "DTMC+PDMP").is_ok());
    }

    #[test]
    fn sanitize_stem_is_predictable() {
        assert_eq!(sanitize_frag_stem("QBasin"), "QBasin");
        assert_eq!(sanitize_frag_stem("$\\wedge$I"), "__wedge_I");
        assert_eq!(
            sanitize_frag_stem("ClosureDiscipline-EXACT (T13)"),
            "ClosureDiscipline-EXACT__T13_"
        );
    }

    // ==================== correspondence (the (b) ratchet) ====================

    #[test]
    fn corr_state_verdicts() {
        let cb = CorrBind {
            entry: "R".into(),
            steele_sha256: "s".into(),
            statements_sha256: "t".into(),
            prose_sha256: "p".into(),
        };
        assert_eq!(corr_state(false, None, "s", "t", "p"), CorrState::Absent);
        // absence outranks a stray recorded triple (prose deleted = uncertified)
        assert_eq!(
            corr_state(false, Some(&cb), "s", "t", "p"),
            CorrState::Absent
        );
        assert_eq!(corr_state(true, None, "s", "t", "p"), CorrState::Unrecorded);
        assert_eq!(
            corr_state(true, Some(&cb), "s", "t", "p"),
            CorrState::Certified
        );
        assert_eq!(
            corr_state(true, Some(&cb), "X", "t", "p"),
            CorrState::Drifted {
                steele: true,
                statements: false,
                prose: false
            }
        );
        // an edited dictionary invalidates its own certification
        assert_eq!(
            corr_state(true, Some(&cb), "s", "X", "Y"),
            CorrState::Drifted {
                steele: false,
                statements: true,
                prose: true
            }
        );
    }

    #[test]
    fn statements_digest_order_independent_and_content_sensitive() {
        let a = vec![
            ("M".to_string(), "x".to_string(), "aa".to_string()),
            ("M".to_string(), "y".to_string(), "bb".to_string()),
        ];
        let b = vec![a[1].clone(), a[0].clone()];
        assert_eq!(statements_digest(&a), statements_digest(&b));
        let c = vec![
            a[0].clone(),
            ("M".to_string(), "y".to_string(), "cc".to_string()),
        ];
        assert_ne!(statements_digest(&a), statements_digest(&c));
    }

    #[test]
    fn correspondence_bindings_merge_dedup_and_conflict() {
        let d = tdir("corr");
        std::fs::write(d.join("book.toml"), META_ONLY).unwrap();
        let row = "[[correspondence]]\nentry = \"R\"\nsteele_sha256 = \"s\"\nstatements_sha256 = \"t\"\nprose_sha256 = \"p\"\n";
        std::fs::write(d.join("bindings.toml.d/R.toml"), row).unwrap();
        // exact duplicate elsewhere: collapses
        std::fs::write(d.join("bindings.toml.d/R2.toml"), row).unwrap();
        let (_, b) = load_book_dir(&d).unwrap();
        assert_eq!(b.correspondences.len(), 1);
        // conflicting triple for the same entry: loud
        std::fs::write(
            d.join("bindings.toml.d/R3.toml"),
            "[[correspondence]]\nentry = \"R\"\nsteele_sha256 = \"OTHER\"\nstatements_sha256 = \"t\"\nprose_sha256 = \"p\"\n",
        )
        .unwrap();
        let e = load_book_dir(&d).unwrap_err();
        assert!(e.contains("two different correspondence triples"), "{e}");
    }
}
