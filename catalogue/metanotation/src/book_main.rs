//! qtsl-book — render the literate rule catalogue.
//!
//! Verbs (rg-style: one obvious verb, rich defaults, works from anywhere):
//!   qtsl-book [render] [--rule ID] [--book D] [--out D] [--no-compile] [--no-receipts]
//!   qtsl-book check
//!   qtsl-book bind [--lean-build DIR | --from-receipts]
//!   qtsl-book api-tex --fragments DIR --out DIR [--api-src DIR] [--entity NOUN]
//!     (emit one \input-able API-block .tex per fragment — the sibling
//!      catalogues' seam: their chapters are hand-authored, so the API
//!      blocks land as per-entry files their sections \input. `check`
//!      also sweeps every book/api-*.toml.d fan, so extraction failures
//!      in sibling fans are loud on the same verb.)
//!
//! Design + staleness semantics: book/DESIGN.md. The tool never runs Lean:
//! receipts are citations (minted where the gate machinery actually runs);
//! `bind` re-anchors hashes, `render` badges drift loudly.

use qtsl_metanotation::book::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn fail(msg: &str) -> ! {
    eprintln!("qtsl-book: {msg}");
    std::process::exit(1);
}

struct Args {
    verb: String,
    rule: Option<String>,
    book_dir: PathBuf,
    out_dir: PathBuf,
    compile: bool,
    receipts: bool,
    lean_build: Option<PathBuf>,
    from_receipts: bool,
    allow_unbuilt: bool,
    keep_moved: bool,
    /// re-stamp correspondence triples: a rule id, or "all". Without it,
    /// recorded triples are kept VERBATIM (pass-marker semantics) and only
    /// first-bound dictionaries are stamped.
    recertify: Option<String>,
    /// additionally emit an \input-able catalogue fragment (preface + stamp
    /// + dashboard + rules + refs, no document shell) at this path, plus its
    /// companion preamble at <stem>-preamble.tex — for hosting the catalogue
    /// as a chapter of another LuaLaTeX document. Full roster only.
    emit_fragment: Option<PathBuf>,
    /// override the API-extraction source root (an mtk toolkit tree);
    /// default: book/api.toml [meta] toolkit_root, else the sibling
    /// mtk repository checkout.
    api_src: Option<PathBuf>,
    /// api-tex: the fragment fan directory (e.g. book/api-system.toml.d).
    fragments: Option<PathBuf>,
    /// api-tex: the sourcenote noun for fragments that don't set
    /// `[api] entity` themselves.
    entity: String,
}

fn parse_args() -> Args {
    let mut a = Args {
        verb: "render".into(),
        rule: None,
        book_dir: manifest_dir().join("book"),
        out_dir: manifest_dir().join("out"),
        compile: true,
        receipts: true,
        lean_build: None,
        from_receipts: false,
        allow_unbuilt: false,
        keep_moved: false,
        recertify: None,
        emit_fragment: None,
        api_src: None,
        fragments: None,
        entity: "entry".into(),
    };
    let mut it = std::env::args().skip(1).peekable();
    if let Some(first) = it.peek() {
        if !first.starts_with('-') {
            a.verb = it.next().unwrap();
        }
    }
    while let Some(x) = it.next() {
        match x.as_str() {
            "--rule" => a.rule = Some(it.next().expect("--rule <id>")),
            "--book" => a.book_dir = PathBuf::from(it.next().expect("--book <dir>")),
            "--out" => a.out_dir = PathBuf::from(it.next().expect("--out <dir>")),
            "--no-compile" => a.compile = false,
            "--no-receipts" => a.receipts = false,
            "--lean-build" => {
                a.lean_build = Some(PathBuf::from(it.next().expect("--lean-build <dir>")))
            }
            "--from-receipts" => a.from_receipts = true,
            "--allow-unbuilt" => a.allow_unbuilt = true,
            "--keep-moved" => a.keep_moved = true,
            "--recertify" => a.recertify = Some(it.next().expect("--recertify <rule-id|all>")),
            "--emit-fragment" => {
                a.emit_fragment = Some(PathBuf::from(it.next().expect("--emit-fragment <path>")))
            }
            "--api-src" => a.api_src = Some(PathBuf::from(it.next().expect("--api-src <dir>"))),
            "--fragments" => {
                a.fragments = Some(PathBuf::from(it.next().expect("--fragments <dir>")))
            }
            "--entity" => a.entity = it.next().expect("--entity <noun>"),
            "--help" | "-h" => {
                eprintln!(
                    "qtsl-book [render|check|bind|api-tex|api-blocks] [--rule ID] [--book D] [--out D] \
                     [--no-compile] [--no-receipts] [--lean-build DIR] [--from-receipts] \
                     [--allow-unbuilt] [--keep-moved] [--recertify RULE-ID|all] \
                     [--emit-fragment PATH] [--api-src DIR] \
                     [--fragments DIR] [--entity NOUN]"
                );
                std::process::exit(0);
            }
            other => fail(&format!("unknown arg: {other}")),
        }
    }
    if !matches!(
        a.verb.as_str(),
        "render" | "check" | "bind" | "api-tex" | "api-blocks"
    ) {
        fail(&format!(
            "unknown verb: {} (render | check | bind | api-tex | api-blocks)",
            a.verb
        ));
    }
    a
}

/// The ed25519 receipt store: `$LEAN_RECEIPT_STORE`, defaulting to
/// `~/.local/share/lean-receipts`. The store is an attestation surface
/// maintained outside this repository; without one, render without
/// `--receipts`.
fn receipt_store() -> PathBuf {
    std::env::var("LEAN_RECEIPT_STORE")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(std::env::var("HOME").expect("HOME")).join(".local/share/lean-receipts")
        })
}

/// The trust-roots file for receipt signature verification:
/// `$TRUST_ROOTS`, or `trust-roots.toml` resolved upward from the crate dir.
fn trust_roots() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("TRUST_ROOTS") {
        let p = PathBuf::from(p);
        return p.is_file().then_some(p);
    }
    let mut d = manifest_dir();
    loop {
        let c = d.join("trust-roots.toml");
        if c.is_file() {
            return Some(c);
        }
        if !d.pop() {
            return None;
        }
    }
}

fn main() {
    let a = parse_args();
    let crate_root = manifest_dir();

    if a.verb == "api-tex" {
        api_tex(&a, &crate_root);
        return;
    }
    // book.toml + book.toml.d/* fragments + bindings.toml + bindings.toml.d/*
    // (the fan seam: one fragment file per catalogue row — see DESIGN.md)
    let (mut bf, bindings) = load_book_dir(&a.book_dir).unwrap_or_else(|e| fail(&e));
    let pages = load_pages(&crate_root, &bf.meta.pages).unwrap_or_else(|e| fail(&e));
    // section order = roster order, a pure function of the pages — never
    // encounter order across fragment files
    canonical_rule_order(&mut bf, &pages).unwrap_or_else(|e| fail(&e));

    if a.verb == "bind" {
        bind(&a, &crate_root, &bf, &pages, &bindings);
        return;
    }

    // ---- receipts scan (shared by check + render) ----
    let modules: HashSet<String> = bf
        .rules
        .iter()
        .flat_map(|r| r.lean.iter().map(|l| l.module.clone()))
        .chain(
            bf.coverage
                .iter()
                .flat_map(|c| c.lean.iter().map(|l| l.module.clone())),
        )
        .collect();
    let receipts = if a.receipts && a.verb != "api-blocks" {
        let roots = trust_roots()
            .unwrap_or_else(|| fail("trust-roots.toml not found (set TRUST_ROOTS or place trust-roots.toml above the crate)"));
        scan_receipts(&receipt_store(), &roots, &modules).unwrap_or_else(|e| fail(&e))
    } else {
        Vec::new()
    };
    eprintln!(
        "{} receipts matched {} bound module(s)",
        receipts.len(),
        modules.len()
    );

    let ctx = BookCtx {
        crate_root: crate_root.clone(),
        store: receipt_store(),
        roots: trust_roots().unwrap_or_default(),
        consult_receipts: a.receipts,
    };

    // ---- API fragments (the producer-surface sections; api.rs) ----
    let api = qtsl_metanotation::api::load_api_dir(&a.book_dir, &crate_root, a.api_src.as_deref())
        .unwrap_or_else(|e| fail(&e));
    // reverse completeness: an api fragment citing no book entry and
    // registered in no standalone group is stale (same union-check
    // posture as the book.toml.d fan seam)
    let standalone_ids: HashSet<&str> = api
        .standalone
        .iter()
        .flat_map(|g| g.ids.iter().map(|s| s.as_str()))
        .collect();
    for id in api.entries.keys() {
        if !bf.rules.iter().any(|r| &r.id == id) && !standalone_ids.contains(id.as_str()) {
            fail(&format!(
                "api.toml.d/{id}.toml cites no [[rule]] entry and no [[standalone]] group — \
                 remove the stale fragment or register its entry"
            ));
        }
    }
    // standalone groups: every listed id has a fragment, and none is
    // also a rule (a rule's block renders inside its rule section)
    for g in &api.standalone {
        for id in &g.ids {
            if !api.entries.contains_key(id) {
                fail(&format!(
                    "[[standalone]] id {id} has no api.toml.d/{id}.toml fragment"
                ));
            }
            if bf.rules.iter().any(|r| &r.id == id) {
                fail(&format!(
                    "[[standalone]] id {id} is also a [[rule]] entry — a rule's API block \
                     renders inside its rule section"
                ));
            }
        }
    }

    // ---- standalone API blocks: emit (api-blocks) or validate ----
    // (extraction runs under check AND render too, so a moved toolkit
    // declaration fails loudly on every path, exactly like rule blocks)
    let render_standalone = |write_out: bool| {
        let repo_root = crate_root.join("../..");
        let rev = git_line(&crate_root, &["rev-parse", "--short", "HEAD"]);
        for g in &api.standalone {
            let dir = repo_root.join(&g.dir);
            if write_out {
                std::fs::create_dir_all(&dir)
                    .unwrap_or_else(|e| fail(&format!("mkdir {}: {e}", dir.display())));
            }
            for (i, id) in g.ids.iter().enumerate() {
                let entry = &api.entries[id];
                let mut tex = format!(
                    "% Auto-generated by `qtsl-book api-blocks` (catalogue/metanotation) at\n\
                     % revision {rev}: the {id} producer-API block, extracted from the mtk\n\
                     % toolkit sources. Do not hand-edit — regenerate with\n\
                     % `qtsl-book api-blocks --api-src <toolkit>` (see book/DESIGN.md,\n\
                     % API sections).\n"
                );
                // the dedup seam: the full note at the group's first
                // entry, the pointer note thereafter (when the group
                // declares one).
                let note = if i > 0 && !g.sourcenote_rest.is_empty() {
                    &g.sourcenote_rest
                } else {
                    &g.sourcenote
                };
                qtsl_metanotation::api::render_api_block_with(entry, &api, note, &mut tex)
                    .unwrap_or_else(|e| fail(&format!("standalone api {id}: {e}")));
                if write_out {
                    let path = dir.join(format!("{id}.tex"));
                    std::fs::write(&path, tex)
                        .unwrap_or_else(|e| fail(&format!("write {}: {e}", path.display())));
                    eprintln!("api-blocks: wrote {}", path.display());
                } else {
                    eprintln!("standalone api {id}: extracted");
                }
            }
        }
    };
    if a.verb == "api-blocks" {
        if api.standalone.is_empty() {
            fail("api-blocks: no [[standalone]] groups in api.toml");
        }
        render_standalone(true);
        return;
    }
    render_standalone(false);

    if a.emit_fragment.is_some() && a.rule.is_some() {
        fail("--emit-fragment renders the full roster; it cannot combine with --rule");
    }
    let emit_mode = a.emit_fragment.is_some();
    let mut selected: Vec<&BookRule> = match &a.rule {
        Some(id) => {
            let r = bf.rules.iter().filter(|r| &r.id == id).collect::<Vec<_>>();
            if r.is_empty() {
                fail(&format!("--rule {id}: no such rule id in book.toml"));
            }
            r
        }
        None => bf.rules.iter().collect(),
    };

    // ---- emit-mode sectioning (design ruling, 2026-07-20): the fragment
    // groups the roster under ToC-visible \section headers drawn from the
    // catalogue's own taxonomy — (page, tier) for the base calculus pages,
    // stratum prefix for the Q-family — with the edge-discipline row
    // (TowerCitation) placed LAST in its own "The Soundness Theorem"
    // section. Emit-time data-driven: rules follow their curated fields,
    // not a hand-list. The standalone volume's flat roster order is
    // untouched (this reorder applies to emit mode only).
    let section_of = |br: &BookRule| -> (u8, &'static str) {
        let row = pages
            .get(&br.source)
            .and_then(|p| p.rules.iter().find(|r| r.name == br.row));
        let (tier, stratum, discipline) = match row {
            Some(r) => (r.tier, r.stratum.as_str(), r.discipline),
            None => (None, "", false),
        };
        if discipline {
            return (99, "The Soundness Theorem");
        }
        // match on the file NAME: the config's page paths carry relative
        // segments ("../BL-rules.toml"), and a raw prefix test against the
        // path silently files every rule under the tier fallback (the
        // 2026-07-21 regression: the rename's re-anchored paths collapsed
        // the emitted chapter from 11 sections to 4).
        let src_name = source_display(&br.source);
        // the composition rules live on the base rules page (folded in
        // from the former AG-rules page); their section is keyed by
        // stratum prefix, like the Q-family, so the fold kept the
        // chapter's section layout byte-stable.
        if stratum.starts_with("BL composition") {
            return (3, "Assume--Guarantee Composition");
        }
        if src_name.starts_with("QTSL") {
            let s = stratum;
            return if s.starts_with("structural") || s.starts_with("battery") {
                (4, "Judgement Structure and Batteries")
            } else if s.starts_with("Streett") || s.starts_with("spec surface") {
                (5, "Streett Rules and the Specification Surface")
            } else if s.starts_with("BL-leaf")
                || s.starts_with("discharge kit")
                || s.starts_with("strict-atom")
                || s.starts_with("arithmetic leaf")
            {
                (6, "Discharge Kits, Closure, and Arithmetic Leaves")
            } else if s.starts_with("Morse") {
                (7, "Morse Topology")
            } else if s.starts_with("composition") || s.starts_with("aggregation") {
                (8, "Composition and Aggregation")
            } else if s.starts_with("distance") {
                (9, "Distance Transport")
            } else {
                eprintln!(
                    "note: rule {} stratum {:?} matched no Q-family cluster — filed under Judgement Structure",
                    br.id, s
                );
                (4, "Judgement Structure and Batteries")
            };
        }
        match tier {
            Some(1) => (1, "Core Structural Rules"),
            _ => (2, "Admissible and Alias Rules"),
        }
    };
    if emit_mode {
        // stable sort: section rank first, curated roster order within
        selected = {
            let mut v: Vec<(usize, &BookRule)> = selected.into_iter().enumerate().collect();
            v.sort_by_key(|(i, br)| (section_of(br).0, *i));
            v.into_iter().map(|(_, br)| br).collect()
        };
    }

    let mut body = String::new();
    let mut parade = String::new();
    let mut covered: HashMap<String, DashRow> = HashMap::new();
    let mut cur_section: Option<(u8, &'static str)> = None;
    for (i, br) in selected.iter().enumerate() {
        if emit_mode {
            let sec = section_of(br);
            if cur_section.map(|c| c.0) != Some(sec.0) {
                let _ = writeln!(body, "\\blcatsection{{{}}}", sec.1);
                if sec.0 == 99 {
                    // generated intro: the assembly-theorem framing, derived
                    // from the rule's own commentary (the first sentence
                    // mentioning soundness, else the first sentence).
                    let intro = derive_soundness_intro(&br.commentary);
                    if !intro.is_empty() {
                        let _ = writeln!(body, "{intro}\n");
                    }
                }
                cur_section = Some(sec);
            }
            // synopsis parade entry (TowerCitation's closes the parade,
            // after a thin separator — the parade ends on the theorem the
            // rules feed)
            let row = pages
                .get(&br.source)
                .and_then(|p| p.rules.iter().find(|r| r.name == br.row))
                .unwrap_or_else(|| fail(&format!("rule {}: row lookup failed", br.id)));
            if section_of(br).0 == 99 {
                parade.push_str("\\paradesep\n");
            }
            parade.push_str(&parade_entry(
                &row.amended,
                &row.name,
                &format!("blcatrule-{}", br.id),
            ));
        }
        let rr = render_rule(&ctx, br, i, &pages, &bindings, &receipts, &bf.meta, &api)
            .unwrap_or_else(|e| fail(&e));
        covered.insert(format!("{}::{}", br.source, br.row), rr.dash.clone());
        body.push_str(&rr.tex);
        body.push('\n');
        eprintln!("rule {}: rendered", br.id);
    }

    // ---- dashboard-only coverage entries (no body sections) ----
    // (a coverage entry colliding with a full [[rule]] entry is caught at
    // load time by the row-uniqueness check, fragments included)
    if a.rule.is_none() {
        for cov in &bf.coverage {
            let (key, dash) =
                coverage_dash(&ctx, cov, &pages, &bindings, &receipts).unwrap_or_else(|e| fail(&e));
            covered.insert(key, dash);
            eprintln!("coverage {}: dashboard row computed", cov.row);
        }
    }

    if a.verb == "check" {
        // sibling-catalogue fans: every book/api-*.toml.d fragment must
        // extract cleanly against the same toolkit tree — the loud-drift
        // guarantee is one verb for all four catalogues.
        let swept = check_sibling_api_fans(&a, &crate_root);
        eprintln!(
            "check: green ({} rule(s), {} sibling api fragment(s))",
            selected.len(),
            swept
        );
        return;
    }

    // ---- assemble ----
    let dashboard = if a.rule.is_none() {
        render_dashboard(&pages, &bf.meta.pages, &covered, &bf.meta.dashboard_intro)
    } else {
        String::new()
    };
    let stamp = format!(
        "Rendered {} \\textperiodcentered{{}} receipts {} \\textperiodcentered{{}} tree \\texttt{{{}{}}}",
        chrono_utc(),
        if a.receipts {
            "signature-verified against the pinned ed25519 trust roots"
        } else {
            "NOT consulted (--no-receipts)"
        },
        git_line(&crate_root, &["rev-parse", "--short", "HEAD"]),
        // dirty = source dirt only; the out/ artefacts this very render is
        // writing must not self-trip the flag.
        if git_line(&crate_root, &["status", "--porcelain", "--", ":/", ":!out"]).is_empty() {
            ""
        } else {
            "+dirty"
        },
    );
    // refs.tex + refs.d/*.tex fragments (per-batch literature additions;
    // duplicate \bibitem keys are loud) — see book.rs::assemble_refs
    let refs = assemble_refs(&a.book_dir).unwrap_or_else(|e| fail(&e));
    let macros = include_str!("../book/catalogue-macros.tex");
    let template = include_str!("../book/book-template.tex");
    let tex = template
        .replace("@@MACROS@@", macros)
        .replace("@@REFS@@", &refs)
        .replace("@@TITLE@@", &bf.meta.title)
        .replace("@@SUBTITLE@@", &bf.meta.subtitle)
        .replace("@@PREFACE@@", &bf.meta.preface)
        .replace("@@STAMP@@", &stamp)
        .replace("@@DASHBOARD@@", &dashboard)
        .replace("@@BODY@@", &body);

    std::fs::create_dir_all(&a.out_dir).expect("mkdir out");
    let base = match &a.rule {
        Some(id) => format!("BL-rule-book-{id}"),
        None => "BL-rule-book".to_string(),
    };
    let tex_path = a.out_dir.join(format!("{base}.tex"));
    if emit_mode {
        // emit mode reorders the roster under section headers; the flat
        // standalone volume is a different artefact — never overwrite it
        // with the emit ordering (render without --emit-fragment for it).
        eprintln!("emit mode: standalone {base}.tex NOT written (fragment only)");
    } else {
        std::fs::write(&tex_path, tex).expect("write tex");
        eprintln!("wrote {}", tex_path.display());
    }

    // ---- includable fragment (catalogue-as-a-chapter of a host document) ----
    if let Some(frag_path) = &a.emit_fragment {
        let rev = git_line(&crate_root, &["rev-parse", "--short", "HEAD"]);
        let dirty =
            if git_line(&crate_root, &["status", "--porcelain", "--", ":/", ":!out"]).is_empty() {
                ""
            } else {
                "+dirty"
            };
        let pre_path = {
            let stem = frag_path
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| fail("--emit-fragment: path has no file stem"));
            frag_path.with_file_name(format!("{stem}-preamble.tex"))
        };
        let provenance = format!(
            "% Auto-generated by the qtsl-book typesetter (Bernstein Logic literate rule\n\
             % catalogue) from the mechanized rule sources, revision {rev}{dirty}.\n\
             % Do not hand-edit: regenerate with `qtsl-book --emit-fragment` and re-copy.\n\
             % Lean statements are extracted from the sources at emission and hash-bound;\n\
             % verifier receipts were signature-verified at emission (their in-text\n\
             % badges record that verification, not a live re-check by the host build).\n\
             % API sections: signatures and construction snippets are extracted from\n\
             % the mtk toolkit sources at emission (book/DESIGN.md, API sections).\n"
        );
        let preamble = format!(
            "{provenance}% This file: packages + macros. Load from the host PREAMBLE, before\n\
             % hyperref. Companion body: {}.\n\n{}",
            frag_path
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default(),
            include_str!("../book/fragment-preamble.tex").replace("@@MACROS@@", macros),
        );
        // refs: fragment mode emits no local thebibliography — the host
        // document resolves the catalogue's \cite keys through its biblatex
        // bibliography (the host carries refs.d/catalogue.bib, key-identical
        // to refs.tex + refs.d/). The standalone volume keeps its own
        // thebibliography via @@REFS@@ above.
        let refs_wrapped = String::from(
            "% references: resolved by the host document's bibliography\n\
             % (fragment mode emits no local thebibliography)\n",
        );
        let body_frag = format!(
            "{provenance}% This file: the catalogue body (preface, stamp, rule synopsis,\n\
             % coverage dashboard, the rules grouped in ToC sections, references).\n\
             % \\input it inside a chapter of a host document whose preamble loaded\n\
             % the companion preamble file.\n\n\
             \\begingroup\n\
             \\setlength{{\\parindent}}{{0pt}}\n\
             \\setlength{{\\parskip}}{{4pt}}\n\n\
             {preface}\n\n\
             \\par\\medskip\n{{\\footnotesize\\textcolor{{NoteGray}}{{{stamp}}}}}\n\n\
             \\blcatsection{{Rule Synopsis}}\n\
             \\sourcenote{{Every rule of the catalogue at a glance: the rule as\n\
             realized in the mechanized development, its name, and the page of\n\
             its full entry. The closing entry, set off by a rule, is the\n\
             assembly-level discipline the numbered rules feed.}}\n\
             \\par\\medskip\n\
             \\begingroup\\small\n\
             {parade}\
             \\endgroup\n\
             \\clearpage\n\
             \\pdfbookmark[1]{{Coverage dashboard}}{{blcat-dashboard}}%\n\
             {dashboard}\n\
             {body}\n\
             {refs_wrapped}\
             \\endgroup\n",
            preface = bf.meta.preface,
        );
        std::fs::write(&pre_path, preamble)
            .unwrap_or_else(|e| fail(&format!("write {}: {e}", pre_path.display())));
        std::fs::write(frag_path, body_frag)
            .unwrap_or_else(|e| fail(&format!("write {}: {e}", frag_path.display())));
        eprintln!("wrote {} + {}", frag_path.display(), pre_path.display());
    }

    if a.compile && emit_mode {
        eprintln!("emit mode: standalone compile skipped (the host build compiles the fragment)");
    }
    if a.compile && !emit_mode {
        let status = Command::new("latexmk")
            .args(["-lualatex", "-interaction=nonstopmode", "-halt-on-error"])
            .arg(format!("{base}.tex"))
            .current_dir(&a.out_dir)
            .status()
            .expect("latexmk not found");
        if !status.success() {
            fail(&format!(
                "latexmk failed — see {}/{base}.log",
                a.out_dir.display()
            ));
        }
        // the glyph gate: lualatex exits 0 on missing glyphs;
        // grep the log and fail loudly.
        let log =
            std::fs::read_to_string(a.out_dir.join(format!("{base}.log"))).unwrap_or_default();
        let missing: Vec<&str> = log
            .lines()
            .filter(|l| l.contains("Missing character"))
            .collect();
        if !missing.is_empty() {
            let mut set: Vec<&str> = missing.iter().take(20).copied().collect();
            set.dedup();
            fail(&format!(
                "glyph gate: {} 'Missing character' line(s) in {base}.log — the PDF silently \
                 dropped glyphs. First offenders:\n{}",
                missing.len(),
                set.join("\n")
            ));
        }
        eprintln!(
            "compiled {} (glyph gate: clean)",
            a.out_dir.join(format!("{base}.pdf")).display()
        );
    }
}

// ============================ api-tex ============================

/// Emit one \input-able API-block .tex file per fragment of a sibling
/// catalogue's fan (api-system.toml.d, …). Extraction failures fail
/// the run loudly — emission IS the drift check for these fans.
fn api_tex(a: &Args, crate_root: &Path) {
    let fragments = a
        .fragments
        .clone()
        .unwrap_or_else(|| fail("api-tex needs --fragments <dir> (e.g. book/api-system.toml.d)"));
    let out_dir = if a.out_dir == manifest_dir().join("out") {
        fail("api-tex needs an explicit --out <dir> (the chapter-side api directory)")
    } else {
        a.out_dir.clone()
    };
    let dir_name = fragments
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| fail("--fragments: path has no directory name"));
    let book_dir = fragments
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| fail("--fragments: path has no parent"));
    let api = qtsl_metanotation::api::load_api_dir_named(
        &book_dir,
        &dir_name,
        crate_root,
        a.api_src.as_deref(),
    )
    .unwrap_or_else(|e| fail(&e));
    if api.entries.is_empty() {
        fail(&format!("no fragments under {}", fragments.display()));
    }
    let rev = git_line(crate_root, &["rev-parse", "--short", "HEAD"]);
    std::fs::create_dir_all(&out_dir).unwrap_or_else(|e| fail(&format!("mkdir out: {e}")));
    for (id, entry) in &api.entries {
        let mut tex = format!(
            "% Auto-generated by `qtsl-book api-tex` from {dir_name}/{id}.toml, revision {rev}.\n\
             % Do not hand-edit: regenerate with\n\
             %   qtsl-book api-tex --fragments <book>/{dir_name} --out <chapters>/api \\\n\
             %     --api-src <mtk toolkit tree>\n\
             % Signatures and construction snippets are extracted from the mtk toolkit\n\
             % sources at emission (book/DESIGN.md, API sections); a missing declaration\n\
             % or marker fails the emission loudly, so quoted code cannot drift silently.\n"
        );
        qtsl_metanotation::api::render_api_block_entity(entry, &api, &mut tex, &a.entity)
            .unwrap_or_else(|e| fail(&format!("{id}: {e}")));
        let path = out_dir.join(format!("{id}.tex"));
        std::fs::write(&path, tex)
            .unwrap_or_else(|e| fail(&format!("write {}: {e}", path.display())));
        eprintln!("api-tex {id}: emitted");
    }
    eprintln!(
        "api-tex: {} block(s) -> {}",
        api.entries.len(),
        out_dir.display()
    );
}

/// `check`'s sweep of the sibling fans: render every fragment of every
/// `book/api-*.toml.d` directory to a scratch string, so a missing
/// declaration, marker, or fixture in ANY catalogue's fan fails the
/// one check verb. Returns the fragment count swept.
fn check_sibling_api_fans(a: &Args, crate_root: &Path) -> usize {
    let mut swept = 0usize;
    let Ok(rd) = std::fs::read_dir(&a.book_dir) else {
        return 0;
    };
    let mut dirs: Vec<String> = rd
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_dir())
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.starts_with("api-") && n.ends_with(".toml.d"))
        .collect();
    dirs.sort();
    for dir_name in dirs {
        let api = qtsl_metanotation::api::load_api_dir_named(
            &a.book_dir,
            &dir_name,
            crate_root,
            a.api_src.as_deref(),
        )
        .unwrap_or_else(|e| fail(&e));
        for (id, entry) in &api.entries {
            let mut tex = String::new();
            qtsl_metanotation::api::render_api_block_entity(entry, &api, &mut tex, "entry")
                .unwrap_or_else(|e| fail(&format!("{dir_name}/{id}: {e}")));
            swept += 1;
        }
        eprintln!(
            "check: {dir_name} — {} fragment(s) extract cleanly",
            api.entries.len()
        );
    }
    swept
}

/// The Soundness Theorem section's one-line intro, derived from the
/// closing rule's own book commentary (never hand-authored here): the
/// first sentence mentioning soundness, else the first sentence.
fn derive_soundness_intro(commentary: &str) -> String {
    // whitespace-collapse first so sentence boundaries at line ends are
    // seen; a "sentence" is a ". "-terminated chunk of the flat text.
    let flat = commentary.split_whitespace().collect::<Vec<_>>().join(" ");
    let sentences: Vec<String> = flat.split_inclusive(". ").map(|s| s.to_string()).collect();
    let pick = sentences
        .iter()
        .find(|s| s.contains("soundness"))
        .or_else(|| sentences.first());
    match pick {
        Some(s) => format!("{{\\itshape {}}}", s.trim()),
        None => String::new(),
    }
}

fn chrono_utc() -> String {
    let out = Command::new("date")
        .args(["-u", "+%Y-%m-%d %H:%M UTC"])
        .output()
        .expect("date");
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

fn git_line(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .expect("git");
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

// ============================ bind ============================

/// Refresh the bindings: statement shas + git blobs always; olean shas
/// from --lean-build (hash the built oleans) or --from-receipts (adopt the
/// newest trusted receipt per module, recording it as provenance).
///
/// Layout (the fan seam): module + HOL-script rows go to the
/// bindings.toml monolith; each book entry's statement rows go to
/// bindings.toml.d/<entry>.toml. A module whose source blob is unchanged
/// since the last bind KEEPS its old row verbatim — so a parallel
/// author's bind is a pure addition (their fragment + any new module
/// rows), untouched modules never churn, and plain `qtsl-book bind` (no
/// mode flag) is legal whenever no bound module moved.
fn bind(
    a: &Args,
    crate_root: &Path,
    bf: &BookFile,
    pages: &BTreeMap<String, qtsl_metanotation::doc::RulesFile>,
    old: &Bindings,
) {
    let mut modules: BTreeMap<String, (String, String, String, String)> = BTreeMap::new(); // module -> (package, olean, prov, blob)
    let mut hol_files: BTreeMap<String, String> = BTreeMap::new(); // script -> blob

    // entry-keyed lean blocks: full rule sections by id, coverage by row
    let entries: Vec<(String, Vec<&LeanRef>)> = bf
        .rules
        .iter()
        .map(|r| (r.id.clone(), r.lean.iter().collect::<Vec<_>>()))
        .chain(
            bf.coverage
                .iter()
                .map(|c| (c.row.clone(), c.lean.iter().collect())),
        )
        .collect();
    let lean_blocks: Vec<&LeanRef> = entries
        .iter()
        .flat_map(|(_, v)| v.iter().copied())
        .collect();

    let receipts = if a.from_receipts {
        let modset: HashSet<String> = lean_blocks.iter().map(|l| l.module.clone()).collect();
        let roots = trust_roots()
            .unwrap_or_else(|| fail("trust-roots.toml not found (set TRUST_ROOTS or place trust-roots.toml above the crate)"));
        scan_receipts(&receipt_store(), &roots, &modset).unwrap_or_else(|e| fail(&e))
    } else {
        Vec::new()
    };

    // ---- module rows: keep-if-unmoved, resolve fresh otherwise ----
    let mut kept = 0usize;
    for lean in &lean_blocks {
        if let Some((pkg_prev, ..)) = modules.get(&lean.module) {
            if *pkg_prev != lean.package {
                fail(&format!(
                    "module {} declared with two packages ({} and {}) across lean blocks",
                    lean.module, pkg_prev, lean.package
                ));
            }
            continue; // already resolved this run
        }
        let src_path = crate_root.join(&lean.src);
        let blob = git_blob_sha(&src_path).unwrap_or_else(|e| fail(&e));
        if let Some(o) = old.modules.iter().find(|m| m.module == lean.module) {
            if o.source_git_blob == blob && o.package == lean.package {
                modules.insert(
                    lean.module.clone(),
                    (
                        o.package.clone(),
                        o.olean_sha256.clone(),
                        o.olean_provenance.clone(),
                        blob,
                    ),
                );
                kept += 1;
                continue;
            }
            // --keep-moved: a moved module keeps its old row VERBATIM (old
            // blob included), so the render's honest ModuleMoved amber
            // survives the bind. The alternative — re-anchoring to the
            // newest receipt while stamping the current blob — would mark
            // the module fresh against a build that predates its source.
            // Use when binding NEW modules without adjudicating old ones.
            if a.keep_moved && o.package == lean.package {
                eprintln!(
                    "bind: {} — source moved since last bind; row kept VERBATIM \
                     (--keep-moved): render badges module-moved until a receipt \
                     for the current source exists and a re-bind adjudicates.",
                    lean.module
                );
                modules.insert(
                    lean.module.clone(),
                    (
                        o.package.clone(),
                        o.olean_sha256.clone(),
                        o.olean_provenance.clone(),
                        o.source_git_blob.clone(),
                    ),
                );
                kept += 1;
                continue;
            }
        }
        let (olean, prov) = if let Some(dir) = &a.lean_build {
            // module Foo.Bar.Baz -> <dir>/**/Foo/Bar/Baz.olean
            let rel: PathBuf = lean.module.split('.').collect::<Vec<_>>().join("/").into();
            let olean_path = find_olean(dir, &rel.with_extension("olean")).unwrap_or_else(|| {
                fail(&format!(
                    "olean for {} not under {}",
                    lean.module,
                    dir.display()
                ))
            });
            let bytes =
                std::fs::read(&olean_path).unwrap_or_else(|e| fail(&format!("read olean: {e}")));
            (
                sha256_hex(&bytes),
                // provenance renders on the page: keep it path-free
                "hashed from the built olean at bind time".to_string(),
            )
        } else if a.from_receipts {
            let newest = receipts
                .iter()
                .rfind(|x| x.module == lean.module && x.trust.contains("TRUSTED"));
            match newest {
                Some(newest) => (
                    newest.olean_sha256.clone(),
                    // provenance renders on the page: receipt id + mint time,
                    // no node labels (export-sanitization posture)
                    format!("bound from receipt {}, {}", newest.sig16, newest.ts),
                ),
                None if a.allow_unbuilt => {
                    eprintln!(
                        "bind: {} — no trusted receipt in the store; binding SOURCE-ONLY \
                         (statements hash-bound, no attested build). Mint a receipt where \
                         the gate machinery runs, then re-bind.",
                        lean.module
                    );
                    (
                        String::new(),
                        "no attested build yet; source-bound only".to_string(),
                    )
                }
                None => fail(&format!(
                    "--from-receipts: no trusted receipt for {} in the store \
                     (pass --allow-unbuilt to bind it source-only, loudly)",
                    lean.module
                )),
            }
        } else {
            fail(&format!(
                "module {} is new or its source moved since the last bind — \
                 resolving its attested build needs --lean-build DIR or \
                 --from-receipts (see DESIGN.md; unmoved modules keep their \
                 rows without either flag)",
                lean.module
            ));
        };
        modules.insert(
            lean.module.clone(),
            (lean.package.clone(), olean, prov, blob),
        );
    }

    // ---- statement rows, gathered per book entry ----
    let mut all_statements: Vec<(String, String, String)> = Vec::new();
    let mut frag_rows: BTreeMap<String, Vec<(String, String, String)>> = BTreeMap::new(); // stem -> rows
    let mut frag_owner: BTreeMap<String, String> = BTreeMap::new(); // stem -> entry key
    for (key, blocks) in &entries {
        let mut rows: Vec<(String, String, String)> = Vec::new();
        for lean in blocks {
            let src_path = crate_root.join(&lean.src);
            let source = std::fs::read_to_string(&src_path)
                .unwrap_or_else(|e| fail(&format!("cannot read {}: {e}", lean.src)));
            for d in &lean.decls {
                let stmt = extract_lean_decl(&source, d)
                    .unwrap_or_else(|e| fail(&format!("{}: {e}", lean.src)));
                rows.push((lean.module.clone(), d.clone(), sha256_hex(stmt.as_bytes())));
            }
            for d in &lean.full_decls {
                let stmt = extract_lean_decl_full(&source, d)
                    .unwrap_or_else(|e| fail(&format!("{}: {e}", lean.src)));
                rows.push((lean.module.clone(), d.clone(), sha256_hex(stmt.as_bytes())));
            }
        }
        if rows.is_empty() {
            continue; // entry cites no Lean; no fragment
        }
        rows.sort();
        rows.dedup();
        let stem = sanitize_frag_stem(key);
        if let Some(prev) = frag_owner.insert(stem.clone(), key.clone()) {
            fail(&format!(
                "entries '{prev}' and '{key}' collide on bindings fragment name {stem}.toml"
            ));
        }
        all_statements.extend(rows.iter().cloned());
        frag_rows.insert(stem, rows);
    }

    for r in &bf.rules {
        if r.hol.status == "ported" && !r.hol.script.is_empty() {
            let p = crate_root.join(&r.hol.script);
            let blob = git_blob_sha(&p).unwrap_or_else(|e| fail(&e));
            hol_files.insert(r.hol.script.clone(), blob);
        }
    }

    // ---- correspondence triples (the (b) ratchet's pass-markers) ----
    // Kept VERBATIM across binds — a bind run for any other reason must
    // never silently launder an unreviewed change into "certified" — and
    // stamped fresh only on the first bind of a new dictionary or under
    // an explicit --recertify. The render compares the recorded triple
    // against the live hashes and badges drift amber.
    if let Some(t) = &a.recertify {
        if t != "all"
            && !bf
                .rules
                .iter()
                .any(|r| r.id == *t && !r.correspondence.is_empty())
        {
            fail(&format!(
                "--recertify {t}: no rule with that id carries a correspondence \
                 dictionary (pass a rule id or 'all')"
            ));
        }
    }
    let mut corr_rows: BTreeMap<String, (String, String, String)> = BTreeMap::new(); // stem -> triple
    for r in &bf.rules {
        if r.correspondence.is_empty() {
            continue;
        }
        let stem = sanitize_frag_stem(&r.id);
        let Some(rows) = frag_rows.get(&stem) else {
            fail(&format!(
                "rule {}: correspondence prose but no bound Lean statements to \
                 certify it against — a dictionary needs both of its sides",
                r.id
            ));
        };
        let recert = match a.recertify.as_deref() {
            Some("all") => true,
            Some(id) => id == r.id,
            None => false,
        };
        let old_triple = old.correspondences.iter().find(|c| c.entry == r.id);
        let triple = match old_triple {
            Some(o) if !recert => (
                o.steele_sha256.clone(),
                o.statements_sha256.clone(),
                o.prose_sha256.clone(),
            ),
            _ => {
                let page = pages.get(&r.source).unwrap_or_else(|| {
                    fail(&format!(
                        "rule {}: source page {} not loaded",
                        r.id, r.source
                    ))
                });
                let row = page
                    .rules
                    .iter()
                    .find(|x| x.name == r.row)
                    .unwrap_or_else(|| {
                        fail(&format!(
                            "rule {}: row '{}' not found in {}",
                            r.id, r.row, r.source
                        ))
                    });
                eprintln!(
                    "bind: {} — correspondence {} against the current \
                     (display, statements, prose) texts",
                    r.id,
                    if old_triple.is_some() {
                        "RE-CERTIFIED (--recertify)"
                    } else {
                        "certified (first bind of this dictionary)"
                    }
                );
                (
                    sha256_hex(row.amended.as_bytes()),
                    statements_digest(rows),
                    sha256_hex(r.correspondence.as_bytes()),
                )
            }
        };
        corr_rows.insert(stem, triple);
    }

    // duplicate (module, decl) pairs across entries collapse to one row —
    // and the same decl cited in two extraction modes (signature vs full)
    // is a defect, not a tolerable ambiguity: the render's lookup is by
    // (module, decl) alone, so two different shas would badge randomly.
    all_statements.sort();
    all_statements.dedup();
    for w in all_statements.windows(2) {
        if w[0].0 == w[1].0 && w[0].1 == w[1].1 {
            fail(&format!(
                "decl {}.{} bound twice with different statement hashes — cited in both \
                 signature-only and full-body mode somewhere; pick one mode per decl",
                w[0].0, w[0].1
            ));
        }
    }

    // ---- write: monolith (modules + HOL scripts) ----
    let mut out = String::from(
        "# bindings.toml — machine-maintained by `qtsl-book bind` (see book/DESIGN.md).\n\
         # Module + HOL-script rows only; per-entry statement rows live in\n\
         # bindings.toml.d/<entry>.toml. Hashes only; hand-prose lives in\n\
         # book.toml + book.toml.d/. Regenerate, never hand-edit.\n\n",
    );
    for (m, (pkg, olean, prov, blob)) in &modules {
        let _ = writeln!(
            out,
            "[[module]]\nmodule = \"{m}\"\npackage = \"{pkg}\"\nolean_sha256 = \"{olean}\"\nolean_provenance = \"{prov}\"\nsource_git_blob = \"{blob}\"\n"
        );
    }
    for (s, blob) in &hol_files {
        let _ = writeln!(
            out,
            "[[hol_file]]\nscript = \"{s}\"\ngit_blob = \"{blob}\"\n"
        );
    }
    let path = a.book_dir.join("bindings.toml");
    std::fs::write(&path, out).unwrap_or_else(|e| fail(&format!("write bindings: {e}")));

    // ---- write: per-entry statement fragments + stale cleanup ----
    let ddir = a.book_dir.join("bindings.toml.d");
    if !frag_rows.is_empty() {
        std::fs::create_dir_all(&ddir)
            .unwrap_or_else(|e| fail(&format!("mkdir {}: {e}", ddir.display())));
    }
    if ddir.is_dir() {
        let stale: Vec<PathBuf> = std::fs::read_dir(&ddir)
            .map(|rd| {
                rd.filter_map(|e| e.ok().map(|e| e.path()))
                    .filter(|p| p.extension().map(|x| x == "toml").unwrap_or(false))
                    .filter(|p| {
                        p.file_stem()
                            .map(|s| !frag_rows.contains_key(&s.to_string_lossy().to_string()))
                            .unwrap_or(false)
                    })
                    .collect()
            })
            .unwrap_or_default();
        for p in stale {
            std::fs::remove_file(&p)
                .unwrap_or_else(|e| fail(&format!("remove stale {}: {e}", p.display())));
            eprintln!(
                "bind: removed stale fragment {} (no book entry cites it)",
                p.display()
            );
        }
    }
    for (stem, rows) in &frag_rows {
        let mut f = format!(
            "# bindings.toml.d/{stem}.toml — machine-maintained by `qtsl-book bind`.\n\
             # Statement hashes cited by book entry '{}'. Regenerate, never hand-edit.\n\n",
            frag_owner[stem]
        );
        for (m, d, sha) in rows {
            let _ = writeln!(
                f,
                "[[statement]]\nmodule = \"{m}\"\ndecl = \"{d}\"\nsha256 = \"{sha}\"\n"
            );
        }
        if let Some((steele, stmts, prose)) = corr_rows.get(stem) {
            let _ = writeln!(
                f,
                "[[correspondence]]\nentry = \"{}\"\nsteele_sha256 = \"{steele}\"\nstatements_sha256 = \"{stmts}\"\nprose_sha256 = \"{prose}\"\n",
                frag_owner[stem]
            );
        }
        std::fs::write(ddir.join(format!("{stem}.toml")), f)
            .unwrap_or_else(|e| fail(&format!("write fragment {stem}: {e}")));
    }

    eprintln!(
        "bind: {} module(s) ({} kept unmoved), {} statement row(s) across {} entry \
         fragment(s), {} correspondence triple(s), {} HOL file(s) -> {} + bindings.toml.d/",
        modules.len(),
        kept,
        all_statements.len(),
        frag_rows.len(),
        corr_rows.len(),
        hol_files.len(),
        path.display()
    );
}

fn find_olean(root: &Path, rel: &Path) -> Option<PathBuf> {
    // search <root> and its lib subdirs for the module-relative olean path
    let direct = root.join(rel);
    if direct.is_file() {
        return Some(direct);
    }
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        let c = d.join(rel);
        if c.is_file() {
            return Some(c);
        }
        if let Ok(rd) = std::fs::read_dir(&d) {
            for e in rd.flatten() {
                let p = e.path();
                if p.is_dir() {
                    stack.push(p);
                }
            }
        }
    }
    None
}
