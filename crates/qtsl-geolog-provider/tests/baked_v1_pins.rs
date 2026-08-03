//! The shared baked-pair pins fixture, checker side: well-formedness,
//! per-closure counter uniqueness, and the binding to the repository's
//! closure-level pins record (`theories/pins/baked_v1_pins.txt`) — the
//! fixture's revision header must carry exactly the minted closure
//! chids that record pins. The producer-side repository commits the
//! byte-identical fixture and binds its generated tables to it; the
//! derived-index mirror assertion (declaration indices decoded from the
//! revision commits themselves) lands with the baked reproduction
//! vocabulary and belongs beside it, not here.

use std::collections::BTreeMap;

const FIXTURE: &str = include_str!("fixtures/baked_v1_pins.txt");
const CLOSURE_PINS: &str = include_str!("../../../theories/pins/baked_v1_pins.txt");

fn revs_of(text: &str, what: &str) -> (String, String) {
    let line = text
        .lines()
        .find(|l| l.starts_with("# revs:"))
        .unwrap_or_else(|| panic!("{what} carries a `# revs:` header"));
    let mut qc = None;
    let mut dc = None;
    for tok in line.trim_start_matches("# revs:").split_whitespace() {
        if let Some(h) = tok.strip_prefix("qc=") {
            qc = Some(h.to_string());
        } else if let Some(h) = tok.strip_prefix("dc=") {
            dc = Some(h.to_string());
        }
    }
    (
        qc.unwrap_or_else(|| panic!("{what}: qc rev in header")),
        dc.unwrap_or_else(|| panic!("{what}: dc rev in header")),
    )
}

#[test]
fn fixture_revs_bind_to_the_closure_pins_record() {
    let (fq, fd) = revs_of(FIXTURE, "fixture");
    let (cq, cd) = revs_of(CLOSURE_PINS, "theories/pins/baked_v1_pins.txt");
    assert_eq!(
        fq, cq,
        "fixture qc rev drifted from the closure pins record"
    );
    assert_eq!(
        fd, cd,
        "fixture dc rev drifted from the closure pins record"
    );
    assert_eq!(fq.len(), 64);
    assert_eq!(fd.len(), 64);
    assert!(fq.bytes().all(|b| b.is_ascii_hexdigit()));
    assert!(fd.bytes().all(|b| b.is_ascii_hexdigit()));
}

#[test]
fn fixture_rows_are_well_formed_and_counter_unique() {
    let mut by_name: BTreeMap<(String, u8), (u8, u32)> = BTreeMap::new();
    let mut by_counter: BTreeMap<(u8, u32), String> = BTreeMap::new();
    let mut rows = 0usize;
    for line in FIXTURE
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
    {
        let mut it = line.split_whitespace();
        let kind = match it.next().expect("kind") {
            "sort" => 0u8,
            "fun" => 1u8,
            other => panic!("unknown pin kind `{other}`"),
        };
        let closure: u8 = it.next().expect("dep").parse().expect("dep index");
        assert!(closure <= 1, "dep indexes the two header revs (0=qc, 1=dc)");
        let ctr: u32 = it.next().expect("counter").parse().expect("counter");
        let name = it.next().expect("name").to_string();
        assert!(it.next().is_none(), "trailing tokens on `{line}`");
        let prev = by_name.insert((name.clone(), closure), (kind, ctr));
        assert!(prev.is_none(), "`{name}` pinned twice at dep {closure}");
        if let Some(other) = by_counter.insert((closure, ctr), name.clone()) {
            panic!("dep {closure} counter {ctr} claimed by both `{other}` and `{name}`");
        }
        rows += 1;
    }
    assert!(rows > 0, "fixture carries rows");
}
