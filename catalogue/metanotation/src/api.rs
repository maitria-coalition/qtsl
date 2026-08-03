//! Producer-API sections — the "API" block every catalogue entry
//! carries: the TypeScript and Rust producer surfaces of the mtk
//! toolkit, rendered as extracted signatures plus a construction
//! snippet quoted from the toolkit's conformance corpus.
//!
//! Data model (the fan seam, same sharding law as `book.toml.d/`):
//! `book/api.toml` carries `[meta]` alone (the toolkit source root);
//! `book/api.toml.d/<entry>.toml` carries exactly one `[api]` table
//! whose file stem equals its `id`. Everything printed is EXTRACTED
//! from the toolkit sources at render time — signatures by declaration
//! name, snippets by fixture-function name, marker pair, or
//! golden-vector name — so quoted code cannot drift silently: a
//! missing declaration or marker fails the render loudly, and what
//! compiles (and byte-conforms) in the corpus is what prints.
//!
//! Source paths in fragments are written in the PUBLIC mtk repository
//! layout (`crates/mtk-catalogue/...`, `ts/...`); the resolver also
//! accepts the workshop layout (same paths minus the `crates/`
//! prefix), so fragments never carry a private path.

use serde::Deserialize;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

// ============================ data model ============================

#[derive(Debug, Deserialize, Default)]
pub struct ApiMetaFile {
    #[serde(default)]
    pub meta: ApiMeta,
    /// standalone API-block groups (the Primitive Catalogue seam):
    /// entries that belong to a hand-authored catalogue chapter rather
    /// than a generated `[[rule]]` section. `qtsl-book api-blocks`
    /// renders each id's block to `<dir>/<id>.tex` for the chapter to
    /// `\input` at its per-entry anchor; `check`/`render` re-extract
    /// them like every rule block, so quoted code cannot drift
    /// silently.
    #[serde(default)]
    pub standalone: Vec<StandaloneGroup>,
}

#[derive(Debug, Deserialize)]
pub struct StandaloneGroup {
    /// output directory for the emitted per-entry `.tex` blocks,
    /// relative to the repository root.
    pub dir: String,
    /// TeX sourcenote for this group's blocks — the rule default
    /// speaks certificate-corpus language; a group states its own
    /// corpus and receipts honestly.
    pub sourcenote: String,
    /// TeX sourcenote for every block after the group's first id —
    /// the dedup seam: the full provenance note prints once, at the
    /// entry the chapter renders first (so `ids` order is the
    /// chapter's render order, and reordering the chapter's entries
    /// means reordering `ids`), and later blocks carry this shorter
    /// pointer back to it. Empty (the default) repeats the full note
    /// at every entry.
    #[serde(default)]
    pub sourcenote_rest: String,
    /// entry ids (fragment stems) in this group.
    pub ids: Vec<String>,
}

#[derive(Debug, Deserialize, Default)]
pub struct ApiMeta {
    /// toolkit source root, crate-relative (default: the sibling mtk
    /// repository checkout, mirroring the experiments chapter's
    /// sibling-clone convention). `--api-src DIR` overrides.
    #[serde(default)]
    pub toolkit_root: String,
}

#[derive(Debug, Deserialize)]
pub struct ApiFragment {
    pub api: ApiEntry,
}

#[derive(Debug, Deserialize)]
pub struct ApiEntry {
    /// book entry id (join key against book.toml.d; file stem by fiat).
    pub id: String,
    /// The entry's noun in the block's sourcenote ("rule", "model
    /// type", "composition pattern"). Empty = the caller's default
    /// (the rule catalogue passes "rule").
    #[serde(default)]
    pub entity: String,
    /// TeX: rendered after the block's sourcenote — family notes (a
    /// parameterized alias builder, a variant argument, a sibling
    /// entry point).
    #[serde(default)]
    pub note: String,
    /// TypeScript surface; None = absent, with `ts_absent` saying why.
    pub ts: Option<LangApi>,
    #[serde(default)]
    pub ts_absent: String,
    /// Rust surface; None = absent, with `rust_absent` saying why.
    pub rust: Option<LangApi>,
    #[serde(default)]
    pub rust_absent: String,
}

#[derive(Debug, Deserialize)]
pub struct LangApi {
    /// rendered handle: the arranged namespace path (TS) or the crate
    /// path (Rust).
    pub handle: String,
    /// signature source file, public-layout-relative.
    pub sig_file: String,
    /// declarations to quote, in order: "fn NAME" | "interface NAME"
    /// | "marker:KEY" (a marker pair in `sig_file` — for surfaces
    /// with no fn/interface declaration form: preset! invocations,
    /// factory consts, type aliases).
    pub sig: Vec<String>,
    /// snippet source file, public-layout-relative. Optional as a
    /// pair with `snippet`: a surface whose conformance corpus holds
    /// no construction at this preview renders signature-only, and
    /// `note` must then say so (absence must say why).
    #[serde(default)]
    pub snippet_file: Option<String>,
    /// "fn-body:NAME" | "marker:KEY" | "conform:VECTOR" (the second
    /// argument of the corpus's `conform("VECTOR", ...)` call).
    #[serde(default)]
    pub snippet: Option<String>,
    /// TeX: a one-line note under this language's snippet (variant
    /// pickers, sibling vectors) — mandatory when `snippet` is absent.
    #[serde(default)]
    pub note: String,
}

// ============================ loading ============================

pub struct ApiCtx {
    pub root: PathBuf,
    pub entries: BTreeMap<String, ApiEntry>,
    pub standalone: Vec<StandaloneGroup>,
}

pub fn load_api_dir(
    book_dir: &Path,
    crate_root: &Path,
    api_src_override: Option<&Path>,
) -> Result<ApiCtx, String> {
    load_api_dir_named(book_dir, "api.toml.d", crate_root, api_src_override)
}

/// As [`load_api_dir`], for a named fan directory beside `api.toml`
/// (the sibling catalogues' seams: `api-system.toml.d`, …). The
/// `[meta]` spine and the toolkit-root resolution are shared.
pub fn load_api_dir_named(
    book_dir: &Path,
    dir_name: &str,
    crate_root: &Path,
    api_src_override: Option<&Path>,
) -> Result<ApiCtx, String> {
    let meta_path = book_dir.join("api.toml");
    let meta_file: ApiMetaFile = if meta_path.is_file() {
        let text = std::fs::read_to_string(&meta_path)
            .map_err(|e| format!("read {}: {e}", meta_path.display()))?;
        toml::from_str::<ApiMetaFile>(&text)
            .map_err(|e| format!("parse {}: {e}", meta_path.display()))?
    } else {
        ApiMetaFile::default()
    };
    let meta = meta_file.meta;
    let root = match api_src_override {
        Some(p) => p.to_path_buf(),
        None => {
            let rel = if meta.toolkit_root.is_empty() {
                "../../../mtk".to_string()
            } else {
                meta.toolkit_root.clone()
            };
            crate_root.join(rel)
        }
    };

    let mut entries = BTreeMap::new();
    let ddir = book_dir.join(dir_name);
    if ddir.is_dir() {
        let mut files: Vec<PathBuf> = std::fs::read_dir(&ddir)
            .map_err(|e| format!("read {}: {e}", ddir.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().map(|x| x == "toml").unwrap_or(false))
            .collect();
        files.sort();
        for f in files {
            let text =
                std::fs::read_to_string(&f).map_err(|e| format!("read {}: {e}", f.display()))?;
            let frag: ApiFragment =
                toml::from_str(&text).map_err(|e| format!("parse {}: {e}", f.display()))?;
            let stem = f
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_default();
            if stem != frag.api.id {
                return Err(format!(
                    "api fragment {} carries id '{}' — stem and id must match",
                    f.display(),
                    frag.api.id
                ));
            }
            if entries.insert(frag.api.id.clone(), frag.api).is_some() {
                return Err(format!("duplicate api entry id in {}", f.display()));
            }
        }
    }
    Ok(ApiCtx {
        root,
        entries,
        standalone: meta_file.standalone,
    })
}

impl ApiCtx {
    /// Resolve a public-layout path under the toolkit root, accepting
    /// the workshop layout (no `crates/` prefix) as a twin.
    fn resolve(&self, public_path: &str) -> Result<PathBuf, String> {
        let a = self.root.join(public_path);
        if a.is_file() {
            return Ok(a);
        }
        if let Some(rest) = public_path.strip_prefix("crates/") {
            let b = self.root.join(rest);
            if b.is_file() {
                return Ok(b);
            }
        }
        Err(format!(
            "API source {public_path} not found under {} (tried the public layout and its \
             workshop twin) — point --api-src at an mtk toolkit tree",
            self.root.display()
        ))
    }

    fn read(&self, public_path: &str) -> Result<String, String> {
        let p = self.resolve(public_path)?;
        std::fs::read_to_string(&p).map_err(|e| format!("read {}: {e}", p.display()))
    }
}

// ============================ extraction ============================

/// Strip the common leading-space indent (ignoring blank lines) and
/// trim blank edge lines.
fn dedent(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start_matches(' ').len())
        .min()
        .unwrap_or(0);
    let mut out: Vec<String> = lines
        .iter()
        .map(|l| {
            if l.trim().is_empty() {
                String::new()
            } else {
                l.get(indent..).unwrap_or(l.trim_start()).to_string()
            }
        })
        .collect();
    while out.first().map(|l| l.is_empty()).unwrap_or(false) {
        out.remove(0);
    }
    while out.last().map(|l| l.is_empty()).unwrap_or(false) {
        out.pop();
    }
    out.join("\n")
}

/// Scanner mode for brace balancing that ignores strings and comments
/// (Rust and TypeScript share enough surface syntax for this use:
/// `//`, `/* */`, `"`, `'`, and backticks with `${}` nesting).
#[derive(Clone, Copy, PartialEq)]
enum Mode {
    Normal,
    LineComment,
    BlockComment,
    Str(char),
}

/// From byte offset `from`, find the first `{` outside strings,
/// comments, and unbalanced parentheses, and its matching `}`.
/// Returns (open, close) byte indexes. The parenthesis condition is
/// what lets a declaration's parameter list carry object-literal
/// types (TypeScript `bindings: { … }`): the brace that opens a
/// parameter's type is inside `(...)` and is not the block open —
/// without the condition, a signature extraction would truncate at
/// the parameter's brace (the H-CONTRACT TypeScript signature was
/// the caught specimen).
fn scan_block(src: &str, from: usize) -> Result<(usize, usize), String> {
    let bytes = src.as_bytes();
    let mut mode = Mode::Normal;
    let mut open = None;
    let mut depth = 0usize;
    let mut paren = 0usize;
    let mut i = from;
    while i < bytes.len() {
        let c = bytes[i] as char;
        match mode {
            Mode::LineComment => {
                if c == '\n' {
                    mode = Mode::Normal;
                }
            }
            Mode::BlockComment => {
                if c == '*' && bytes.get(i + 1) == Some(&b'/') {
                    mode = Mode::Normal;
                    i += 1;
                }
            }
            Mode::Str(q) => {
                if c == '\\' {
                    i += 1;
                } else if c == q {
                    mode = Mode::Normal;
                } else if q == '`' && c == '$' && bytes.get(i + 1) == Some(&b'{') {
                    // template-literal interpolation: balance it as code
                    // (rare in our corpora; conservative handling)
                    let (o, cl) = scan_block(src, i + 1)?;
                    debug_assert_eq!(o, i + 1);
                    i = cl;
                }
            }
            Mode::Normal => match c {
                '/' if bytes.get(i + 1) == Some(&b'/') => mode = Mode::LineComment,
                '/' if bytes.get(i + 1) == Some(&b'*') => mode = Mode::BlockComment,
                '"' => mode = Mode::Str('"'),
                '\'' => {
                    // Rust lifetimes ('a) are not string opens; treat a
                    // quote as a char/string literal only if it closes
                    // nearby. Cheap disambiguation good enough for the
                    // corpora: look for a closing quote within 3 bytes.
                    let close_near = (1..=3).any(|k| bytes.get(i + k) == Some(&b'\''));
                    if close_near {
                        mode = Mode::Str('\'');
                    }
                }
                '`' => mode = Mode::Str('`'),
                '(' if open.is_none() => paren += 1,
                ')' if open.is_none() => paren = paren.saturating_sub(1),
                '{' => {
                    if open.is_none() {
                        if paren == 0 {
                            open = Some(i);
                            depth = 1;
                        }
                        // a brace inside parentheses before the block
                        // opens is parameter-type structure, not the
                        // block; its mate falls to the no-open arm of
                        // '}' below.
                    } else {
                        depth += 1;
                    }
                }
                '}' => {
                    if open.is_some() {
                        depth -= 1;
                        if depth == 0 {
                            return Ok((open.unwrap(), i));
                        }
                    }
                }
                _ => {}
            },
        }
        i += 1;
    }
    Err("unbalanced braces (no block found)".to_string())
}

/// Locate the start-of-line byte offset of a declaration.
/// `kind` ∈ {"fn", "interface"}; matching is line-anchored so call
/// sites never match. Two passes: exported/pub declaration forms
/// first; a bare class-method form (`name(` at line start) only when
/// no exported form exists anywhere in the file.
fn find_decl(src: &str, kind: &str, name: &str) -> Result<usize, String> {
    let boundary = |rest: &str, extra_ws: bool| match rest.chars().next() {
        Some('(') | Some('<') => true,
        Some(' ') | Some('{') => extra_ws,
        _ => false,
    };
    let scan = |bare_methods: bool| -> Option<usize> {
        let mut offset = 0usize;
        for line in src.split_inclusive('\n') {
            let t = line.trim_start();
            let hit = match kind {
                "fn" => {
                    let after = |p: &str| {
                        t.strip_prefix(p)
                            .and_then(|r| r.strip_prefix(name))
                            .map(|rest| boundary(rest, false))
                            .unwrap_or(false)
                    };
                    if bare_methods {
                        // class methods, instance (`name(`) or static
                        // (`static name(`) — TS class members carry no
                        // `function` keyword.
                        t.strip_prefix("static ")
                            .unwrap_or(t)
                            .strip_prefix(name)
                            .map(|rest| boundary(rest, false))
                            .unwrap_or(false)
                    } else {
                        after("pub fn ")
                            || after("fn ")
                            || after("export function ")
                            || after("export async function ")
                            || after("function ")
                            || after("async function ")
                    }
                }
                "interface" => {
                    !bare_methods
                        && t.strip_prefix("export interface ")
                            .or_else(|| t.strip_prefix("interface "))
                            .and_then(|r| r.strip_prefix(name))
                            .map(|rest| boundary(rest, true))
                            .unwrap_or(false)
                }
                _ => false,
            };
            if hit {
                // line start (indent included): extraction dedents the
                // whole block, so continuation lines align with line one.
                return Some(offset);
            }
            offset += line.len();
        }
        None
    };
    if kind != "fn" && kind != "interface" {
        return Err(format!("unknown decl kind '{kind}'"));
    }
    scan(false)
        .or_else(|| if kind == "fn" { scan(true) } else { None })
        .ok_or_else(|| format!("declaration '{kind} {name}' not found"))
}

/// Signature: from the decl start to (exclusive) its opening brace.
/// The "marker" kind quotes a marker-pair region verbatim instead —
/// the signature form for surfaces with no fn/interface declaration.
fn extract_sig(src: &str, kind: &str, name: &str) -> Result<String, String> {
    if kind == "marker" {
        return extract_marker(src, name);
    }
    let start = find_decl(src, kind, name)?;
    if kind == "interface" {
        // interfaces quote whole: fields are the signature.
        let (_, close) = scan_block(src, start)?;
        return Ok(dedent(&src[start..=close]));
    }
    let (open, _) = scan_block(src, start)?;
    Ok(dedent(src[start..open].trim_end()))
}

/// Function body (fixture snippets): the inside of the decl's braces.
fn extract_fn_body(src: &str, name: &str) -> Result<String, String> {
    let start = find_decl(src, "fn", name)?;
    let (open, close) = scan_block(src, start)?;
    Ok(dedent(&src[open + 1..close]))
}

/// Marker region: lines strictly between `// book: api begin KEY` and
/// `// book: api end KEY`.
fn extract_marker(src: &str, key: &str) -> Result<String, String> {
    let begin = format!("book: api begin {key}");
    let end = format!("book: api end {key}");
    let mut collecting = false;
    let mut out: Vec<&str> = Vec::new();
    for line in src.lines() {
        let t = line.trim().trim_start_matches('/').trim();
        if t == begin {
            if collecting {
                return Err(format!("marker '{key}': nested begin"));
            }
            collecting = true;
            continue;
        }
        if t == end {
            if !collecting {
                return Err(format!("marker '{key}': end before begin"));
            }
            return Ok(dedent(&out.join("\n")));
        }
        if collecting {
            out.push(line);
        }
    }
    Err(format!(
        "marker '{key}' not found (expected `// book: api begin {key}` … `// book: api end {key}`)"
    ))
}

/// The construction expression: the second argument of the corpus call
/// `conform("VECTOR", <expr>)`.
fn extract_conform(src: &str, vector: &str) -> Result<String, String> {
    let needle = "conform(";
    let want = format!("\"{vector}\"");
    let mut search_from = 0usize;
    while let Some(rel) = src[search_from..].find(needle) {
        let call = search_from + rel;
        let args_start = call + needle.len();
        // split the call's top-level arguments with the mode-aware scanner
        let bytes = src.as_bytes();
        let mut mode = Mode::Normal;
        let mut depth = 1usize; // inside conform's '('
        let mut i = args_start;
        let mut arg_start = args_start;
        let mut args: Vec<(usize, usize)> = Vec::new();
        while i < bytes.len() && depth > 0 {
            let c = bytes[i] as char;
            match mode {
                Mode::LineComment => {
                    if c == '\n' {
                        mode = Mode::Normal;
                    }
                }
                Mode::BlockComment => {
                    if c == '*' && bytes.get(i + 1) == Some(&b'/') {
                        mode = Mode::Normal;
                        i += 1;
                    }
                }
                Mode::Str(q) => {
                    if c == '\\' {
                        i += 1;
                    } else if c == q {
                        mode = Mode::Normal;
                    }
                }
                Mode::Normal => match c {
                    '/' if bytes.get(i + 1) == Some(&b'/') => mode = Mode::LineComment,
                    '/' if bytes.get(i + 1) == Some(&b'*') => mode = Mode::BlockComment,
                    '"' => mode = Mode::Str('"'),
                    '\'' => mode = Mode::Str('\''),
                    '`' => mode = Mode::Str('`'),
                    '(' | '[' | '{' => depth += 1,
                    ')' | ']' | '}' => {
                        depth -= 1;
                        if depth == 0 {
                            args.push((arg_start, i));
                        }
                    }
                    ',' if depth == 1 => {
                        args.push((arg_start, i));
                        arg_start = i + 1;
                    }
                    _ => {}
                },
            }
            i += 1;
        }
        if args.len() >= 2 && src[args[0].0..args[0].1].trim() == want {
            let snippet = dedent(src[args[1].0..args[1].1].trim_matches('\n'));
            let flat = snippet.trim();
            let trivial = !flat.is_empty()
                && flat
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '$' || c == '.');
            if trivial {
                return Err(format!(
                    "conform '{vector}': the corpus binds the construction to a variable \
                     ('{flat}') — wrap the construction site with a marker pair and use \
                     snippet = \"marker:KEY\" instead"
                ));
            }
            return Ok(snippet);
        }
        search_from = args_start;
    }
    Err(format!("no conform(\"{vector}\", …) call found"))
}

fn extract_snippet(src: &str, spec: &str) -> Result<String, String> {
    match spec.split_once(':') {
        Some(("fn-body", name)) => extract_fn_body(src, name),
        Some(("marker", key)) => extract_marker(src, key),
        Some(("conform", vector)) => extract_conform(src, vector),
        _ => Err(format!(
            "snippet spec '{spec}' — expected fn-body:NAME | marker:KEY | conform:VECTOR"
        )),
    }
}

fn parse_sig_spec(spec: &str) -> Result<(&str, &str), String> {
    if let Some(key) = spec.strip_prefix("marker:") {
        return Ok(("marker", key));
    }
    spec.split_once(' ')
        .filter(|(k, _)| matches!(*k, "fn" | "interface"))
        .ok_or_else(|| {
            format!(
                "sig spec '{spec}' — expected \"fn NAME\", \"interface NAME\", or \"marker:KEY\""
            )
        })
}

// ============================ rendering ============================

fn tex_tt(s: &str) -> String {
    s.replace('\\', "\\textbackslash{}")
        .replace('_', "\\_")
        .replace('#', "\\#")
        .replace('$', "\\$")
        .replace('%', "\\%")
        .replace('&', "\\&")
        .replace('~', "\\textasciitilde{}")
}

fn verbatim(env: &str, text: &str) -> String {
    // a stray \end{env} inside quoted code would end the environment
    // early; no corpus source contains one, but fail loudly if ever.
    format!("\\begin{{{env}}}\n{}\n\\end{{{env}}}\n", text.trim_end())
}

fn render_lang(
    tex: &mut String,
    ctx: &ApiCtx,
    lang_name: &str,
    env: &str,
    lang: &LangApi,
) -> Result<(), String> {
    let _ = writeln!(tex, "\\apilang{{{lang_name}}}{{{}}}", tex_tt(&lang.handle));
    let sig_src = ctx.read(&lang.sig_file)?;
    let mut sig_texts: Vec<String> = Vec::new();
    for spec in &lang.sig {
        let (kind, name) = parse_sig_spec(spec)?;
        let sig =
            extract_sig(&sig_src, kind, name).map_err(|e| format!("{}: {e}", lang.sig_file))?;
        if sig.contains(&format!("\\end{{{env}}}")) {
            return Err(format!(
                "{spec}: extracted text closes the verbatim environment"
            ));
        }
        sig_texts.push(sig);
    }
    let _ = writeln!(
        tex,
        "\\apiprov{{signature --- \\texttt{{{}}}}}",
        tex_tt(&lang.sig_file)
    );
    tex.push_str(&verbatim(env, &sig_texts.join("\n\n")));

    match (&lang.snippet_file, &lang.snippet) {
        (Some(snippet_file), Some(snippet_spec)) => {
            let snip_src = ctx.read(snippet_file)?;
            let snippet = extract_snippet(&snip_src, snippet_spec)
                .map_err(|e| format!("{snippet_file}: {e}"))?;
            if snippet.contains(&format!("\\end{{{env}}}")) {
                return Err(format!(
                    "{snippet_spec}: extracted snippet closes the verbatim environment"
                ));
            }
            let _ = writeln!(
                tex,
                "\\apiprov{{construction --- \\texttt{{{}}}}}",
                tex_tt(snippet_file)
            );
            tex.push_str(&verbatim(env, &snippet));
        }
        (None, None) => {
            // signature-only surface: legal iff the note says why the
            // corpus holds no construction (absence must say why).
            if lang.note.is_empty() {
                return Err(format!(
                    "{}: no snippet and no note — a signature-only surface must say why \
                     the conformance corpus holds no construction",
                    lang.handle
                ));
            }
        }
        _ => {
            return Err(format!(
                "{}: snippet and snippet_file must be given together",
                lang.handle
            ))
        }
    }
    if !lang.note.is_empty() {
        let _ = writeln!(tex, "\\apiprov{{{}}}", lang.note);
    }
    Ok(())
}

/// The rule-catalogue-family sourcenote (certificate-corpus
/// receipts), with the entry's noun substituted — "rule", "model
/// type", "composition pattern". One copy of the text, so the three
/// generated catalogues cannot drift from the Rule Catalogue's block
/// style; the standalone groups replace it wholesale through
/// [`render_api_block_with`] (each group names its own corpus and
/// receipts honestly).
fn sourcenote_for(entity: &str) -> String {
    format!(
        "Producer surface of the \\texttt{{mtk}} toolkit for this {entity}: the \
         TypeScript arrangement (npm package \\texttt{{@maitria/mtk}}) and the Rust catalogue \
         crate (\\texttt{{crates/mtk-catalogue}}) --- one Rust implementation underneath, \
         reached from TypeScript in-process through a native binding, so the two surfaces \
         cannot diverge. Signatures and constructions are extracted from the toolkit sources \
         at every regeneration of this catalogue; each construction is quoted verbatim from \
         the toolkit's conformance corpus, code whose emitted certificate bytes are verified \
         byte-identical against the committed golden vectors (helper values named \
         \\texttt{{fx\\_*}} or \\texttt{{f.*}} are that corpus's shared fixtures, defined \
         beside the quoted lines). This API constructs and emits; it never checks --- the \
         checker re-derives every claim independently."
    )
}

/// The per-entry API block: `\ruleblock{API}`, sourcenote, TypeScript
/// then Rust (each: handle, signature, corpus construction). The rule
/// catalogue's entry point; sibling catalogues pass their own default
/// noun through [`render_api_block_entity`].
pub fn render_api_block(entry: &ApiEntry, ctx: &ApiCtx, tex: &mut String) -> Result<(), String> {
    render_api_block_entity(entry, ctx, tex, "rule")
}

/// [`render_api_block`] with the sourcenote noun chosen by the caller
/// (overridden per-fragment by `[api] entity`).
pub fn render_api_block_entity(
    entry: &ApiEntry,
    ctx: &ApiCtx,
    tex: &mut String,
    default_entity: &str,
) -> Result<(), String> {
    let entity = if entry.entity.is_empty() {
        default_entity
    } else {
        &entry.entity
    };
    render_api_block_with(entry, ctx, &sourcenote_for(entity), tex)
}

/// Same block with a caller-supplied sourcenote — the standalone
/// groups' path (each group names its own corpus and receipts).
pub fn render_api_block_with(
    entry: &ApiEntry,
    ctx: &ApiCtx,
    sourcenote: &str,
    tex: &mut String,
) -> Result<(), String> {
    let _ = writeln!(tex, "\\ruleblock{{API}}");
    let _ = writeln!(tex, "\\sourcenote{{{sourcenote}}}");
    if !entry.note.is_empty() {
        tex.push_str(&entry.note);
        tex.push('\n');
    }
    match (&entry.ts, entry.ts_absent.is_empty()) {
        (Some(l), _) => render_lang(tex, ctx, "TypeScript", "tssrc", l)
            .map_err(|e| format!("TypeScript: {e}"))?,
        (None, false) => {
            let _ = writeln!(tex, "\\apilang{{TypeScript}}{{---}}");
            let _ = writeln!(tex, "{}", entry.ts_absent);
        }
        (None, true) => {
            return Err("no [api.ts] and no ts_absent reason — absence must say why".into())
        }
    }
    match (&entry.rust, entry.rust_absent.is_empty()) {
        (Some(l), _) => {
            render_lang(tex, ctx, "Rust", "rustsrc", l).map_err(|e| format!("Rust: {e}"))?
        }
        (None, false) => {
            let _ = writeln!(tex, "\\apilang{{Rust}}{{---}}");
            let _ = writeln!(tex, "{}", entry.rust_absent);
        }
        (None, true) => {
            return Err("no [api.rust] and no rust_absent reason — absence must say why".into())
        }
    }
    Ok(())
}

// ============================ tests ============================

#[cfg(test)]
mod tests {
    use super::*;

    const RUST_SRC: &str = r#"
impl Foo {
    /// Rule catalogue: `Ax`.
    pub fn ax(&mut self, formula: Formula) -> ProofRef {
        self.push(formula)
    }

    pub fn weaken(
        &mut self,
        premise: ProofRef,
        extra: Formula,
    ) -> Result<ProofRef, Refusal> {
        let s = "a { brace in a string";
        self.check(premise, extra)
    }
}

pub fn fx_thing() -> Row {
    let kit = Kit { a: 1, b: 2 };
    build(kit).unwrap()
}
"#;

    const TS_SRC: &str = r#"
export interface SafetyBatteryArgs {
  readonly kit: SafetyKit;
  readonly p: QLike;
}

export function safetyBattery(args: SafetyBatteryArgs): R<SafetyBatteryRow> {
  return native(args);
}

class B {
  andI(left: ProofRef, right: ProofRef): Result<ProofRef, Refusal> {
    return rowResult(this.b.andI(left, right));
  }

  static fromBytes(bytes: Uint8Array): Result<B, Refusal> {
    return graphResult(native.fromBytes(bytes));
  }
}

test("x", () => {
  // book: api begin demo
  const row = c.thing({ a: 1 });
  // book: api end demo
  conform(
    "qtsl_demo.v0.cbor",
    u(
      c.towerCitation({
        child: f.jr("qregionsat", 0),
        p: "4/5",
      }),
    ).cbor,
  );
  conform("qtsl_bound.v0.cbor", battery.cbor);
});
"#;

    #[test]
    fn rust_sig_and_body() {
        let sig = extract_sig(RUST_SRC, "fn", "weaken").unwrap();
        assert!(sig.starts_with("pub fn weaken("));
        assert!(sig.ends_with("Result<ProofRef, Refusal>"));
        assert!(!sig.contains('{'));
        let body = extract_fn_body(RUST_SRC, "fx_thing").unwrap();
        assert_eq!(body, "let kit = Kit { a: 1, b: 2 };\nbuild(kit).unwrap()");
        // brace inside a string must not break balancing
        let body2 = extract_fn_body(RUST_SRC, "weaken").unwrap();
        assert!(body2.contains("a { brace in a string"));
    }

    #[test]
    fn ts_sig_method_interface() {
        let s = extract_sig(TS_SRC, "fn", "safetyBattery").unwrap();
        assert!(s.starts_with("export function safetyBattery"));
        let m = extract_sig(TS_SRC, "fn", "andI").unwrap();
        assert!(m.starts_with("andI(left"));
        let st = extract_sig(TS_SRC, "fn", "fromBytes").unwrap();
        assert!(st.starts_with("static fromBytes(bytes"));
        assert!(st.ends_with("Result<B, Refusal>"));
        let i = extract_sig(TS_SRC, "interface", "SafetyBatteryArgs").unwrap();
        assert!(i.starts_with("export interface SafetyBatteryArgs {"));
        assert!(i.ends_with('}'));
    }

    #[test]
    fn ts_sig_object_literal_param() {
        // a parameter whose TYPE is an object literal opens a brace
        // inside the parentheses; the signature must run to the body
        // brace, not truncate at the parameter's (the H-CONTRACT
        // specimen, caught on the rendered page).
        let src = "class B {\n  contract(\n    inputs: ReadonlyArray<Wire>,\n    bindings: {\n      extents: ReadonlyArray<number>;\n    },\n  ): Result<Wire, Refusal> {\n    return go(inputs, bindings);\n  }\n}\n";
        let s = extract_sig(src, "fn", "contract").unwrap();
        assert!(s.contains("extents"), "object-literal param retained: {s}");
        assert!(
            s.ends_with("Result<Wire, Refusal>"),
            "return type retained: {s}"
        );
        // and the body extraction lands on the body, not the param
        let b = extract_fn_body(src, "contract").unwrap();
        assert!(b.contains("return go"), "body is the body: {b}");
        assert!(!b.contains("extents"), "param type is not the body: {b}");
    }

    #[test]
    fn marker_and_conform() {
        let m = extract_marker(TS_SRC, "demo").unwrap();
        assert_eq!(m, "const row = c.thing({ a: 1 });");
        let c = extract_conform(TS_SRC, "qtsl_demo.v0.cbor").unwrap();
        assert!(c.starts_with("u("));
        assert!(c.ends_with(").cbor"));
        assert!(c.contains("towerCitation"));
        // a variable-bound construction is refused with routing advice
        let e = extract_conform(TS_SRC, "qtsl_bound.v0.cbor").unwrap_err();
        assert!(e.contains("marker"));
    }

    #[test]
    fn missing_is_loud() {
        assert!(extract_sig(RUST_SRC, "fn", "nope").is_err());
        assert!(extract_marker(TS_SRC, "nope").is_err());
        assert!(extract_conform(TS_SRC, "nope.v0.cbor").is_err());
    }

    #[test]
    fn sig_marker_and_plain_function_decls() {
        // Sibling-catalogue seams: a sig spec may be a marker pair
        // (surfaces with no fn/interface declaration form) …
        assert_eq!(parse_sig_spec("marker:demo").unwrap(), ("marker", "demo"));
        assert_eq!(
            extract_sig(TS_SRC, "marker", "demo").unwrap(),
            "const row = c.thing({ a: 1 });"
        );
        // … and non-exported TS helpers ("function name(") are
        // declaration forms too (test-corpus fixture builders).
        let src = "function buildSde(sys: S) {\n  return sys.sde({ a: 1 });\n}\n";
        assert_eq!(
            extract_fn_body(src, "buildSde").unwrap(),
            "return sys.sde({ a: 1 });"
        );
    }
}
