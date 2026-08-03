//! The content-addressed store seam (design point F-3):
//! pure lookup behind the store-seam evaluator families
//! (`qtsl_kcite_wf`, the circuit fragment of
//! `qtsl_tr_grain`/`qtsl_tr_endo`, `qtsl_gate_scalar`).
//!
//! The theory's own scoping line makes this seam load-bearing:
//! kernel citations are "checked where the cited content is
//! reachable" (C-JD-KCITE), so reachability is part of the verdict
//! semantics — an absent store object is REFUSAL fuel at the
//! evaluator, never a guessed verdict, and no verdict semantics live
//! here. Claims stay vocabulary-gated: a provider constructed with no
//! store still claims the store-seam relations and refuses
//! per-instance with the case named (loud beats silent — the s5c F-2
//! lesson: silent un-claiming is invisible).

use std::collections::BTreeMap;
use std::path::PathBuf;

/// Content-addressed store access for evaluators whose subject cites
/// hypernets by digest. Pure lookup: no verdict semantics live here.
///
/// `Send + Sync` supertraits: the provider is one shared value behind
/// the plugin seam (test fixtures hold it in statics; engine hosts may
/// share it across threads), and an attached store rides along.
pub trait StoreResolver: Send + Sync {
    /// The bytes for a sha256 digest (hex, lowercase), or `None` if
    /// the store cannot reach them. `None` is refusal fuel at the
    /// evaluator, never a guess.
    fn fetch(&self, digest_hex: &str) -> Option<Vec<u8>>;
}

/// The landed on-disk convention: `<store_dir>/<digest-hex>.axhn`
/// (the atari corpus layout — `atari_provider.rs`, whose
/// driver-local walks this seam's families port).
#[derive(Debug, Clone)]
pub struct DirStore(pub PathBuf);

impl StoreResolver for DirStore {
    fn fetch(&self, digest_hex: &str) -> Option<Vec<u8>> {
        std::fs::read(self.0.join(format!("{digest_hex}.axhn"))).ok()
    }
}

/// An in-memory store: battery mutants become byte surgery — no
/// tempdir choreography — and downstream driver tests want it
/// too.
#[derive(Debug, Clone, Default)]
pub struct MemStore(BTreeMap<String, Vec<u8>>);

impl MemStore {
    pub fn new() -> MemStore {
        MemStore::default()
    }

    /// Bind `digest_hex` to `bytes`. The binding is whatever the
    /// caller says — batteries deliberately bind wrong bytes to probe
    /// the decode and digest gates.
    pub fn insert(&mut self, digest_hex: impl Into<String>, bytes: Vec<u8>) {
        self.0.insert(digest_hex.into(), bytes);
    }
}

impl FromIterator<(String, Vec<u8>)> for MemStore {
    fn from_iter<T: IntoIterator<Item = (String, Vec<u8>)>>(iter: T) -> MemStore {
        MemStore(iter.into_iter().collect())
    }
}

impl StoreResolver for MemStore {
    fn fetch(&self, digest_hex: &str) -> Option<Vec<u8>> {
        self.0.get(digest_hex).cloned()
    }
}
