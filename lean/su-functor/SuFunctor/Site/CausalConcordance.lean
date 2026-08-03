import SuFunctor.Site.WavyCoverage
import QtslAux.DiamondTopology

/-! # The site concordance: the classical window site is the derived
diamond site of the causal order `(ℝ, ≤, <)`

The spacetime site, extracted from the causal order — the concordance
half.  `QtslAux.DiamondTopology` derives, from any causal order carrying
a `ChronologyKit` (the Martin–Panangaden bicontinuity fragment), a
Grothendieck topology on its diamonds: covers are the chronologically
interior subdiamonds.  This module proves that the house's classical
window site is **exactly** that construction's value at the causal order
`(ℝ, ≤, <)`:

* `Window.toDiamond` / `Window.ofDiamond` — the identification of
  anchored windows with diamonds of `ℝ`, inverse on the nose (structure
  eta; the `le` fields are proofs);
* `le_iff` and `strictlyInterior_iff` — containment and strict
  interiority correspond **definitionally** (`Iff.rfl`): the window
  grammar was already speaking the causal-order vocabulary;
* `mem_interiorTopology_iff_derived` — **the concordance keystone**: a
  sieve covers `W` in the landed `interiorTopology` iff its pushforward
  covers `toDiamond W` in the derived `diamondTopology` of
  `linearOrderKit ℝ`.  The house window site's coverage is not *like*
  the causal order's derived coverage; it *is* it.
* `wavy_mem_iff_derived` — composed with the landed translation-quotient
  correspondence (`mem_interiorTopology_iff`): the book's base site
  itself — durations with wavy covers — corresponds cover-for-cover with
  the derived diamond site of `(ℝ, ≤, <)` through the anchor quotient.

Together with the Minkowski kit (`QtslAux.DiamondTopology`), this places
the classical site as the `(0+1)`-dimensional value of one uniform
construction — *site from causal order* — whose other values include
special relativity (any dimension, kernel-checked) and, by
Martin–Panangaden's theorems, every globally hyperbolic spacetime
(cited, not formalized: no Lorentzian geometry is mechanized here).
-/

namespace SuFunctor

namespace Site

namespace TTT

noncomputable section

open CategoryTheory
open Qtsl.DiamondSite

/-! ## Windows as diamonds of `(ℝ, ≤)` -/

/-- A window is a diamond of the causal order `ℝ`. -/
def Window.toDiamond (W : Window) : Diamond ℝ := ⟨W.d, W.u, W.dle⟩

/-- A diamond of `ℝ` is a window. -/
def Window.ofDiamond (D : Diamond ℝ) : Window := ⟨D.lo, D.hi, D.le⟩

@[simp] theorem Window.toDiamond_ofDiamond (D : Diamond ℝ) :
    (Window.ofDiamond D).toDiamond = D := rfl

@[simp] theorem Window.ofDiamond_toDiamond (W : Window) :
    Window.ofDiamond W.toDiamond = W := rfl

/-- Containment corresponds definitionally. -/
theorem Window.le_iff {W' W : Window} :
    W' ≤ W ↔ W'.toDiamond ≤ W.toDiamond :=
  Iff.rfl

/-- The inverse direction, at the diamond end. -/
theorem Window.ofDiamond_le_iff {E : Diamond ℝ} {W : Window} :
    Window.ofDiamond E ≤ W ↔ E ≤ W.toDiamond :=
  Iff.rfl

/-- **Strict interiority is derived interiority** — definitionally: the
window grammar's `StrictlyInterior` is the chronological-interiority
relation of the causal order `(ℝ, <)`, read through the diamond
identification.  (`InteriorMem` takes the outer diamond first.) -/
theorem Window.strictlyInterior_iff {W' W : Window} :
    W'.StrictlyInterior W ↔
      InteriorMem (linearOrderKit ℝ) W.toDiamond W'.toDiamond :=
  Iff.rfl

/-- The diamond-end form. -/
theorem Window.strictlyInterior_ofDiamond_iff {E : Diamond ℝ} {W : Window} :
    (Window.ofDiamond E).StrictlyInterior W ↔
      InteriorMem (linearOrderKit ℝ) W.toDiamond E :=
  Iff.rfl

/-- The identification is monotone — indeed definitionally so. -/
theorem Window.monotone_toDiamond : Monotone Window.toDiamond :=
  fun _ _ h => h

/-- The identification as a functor of the poset categories. -/
def windowToDiamond : Window ⥤ Diamond ℝ :=
  Window.monotone_toDiamond.functor

@[simp] theorem windowToDiamond_obj (W : Window) :
    windowToDiamond.obj W = W.toDiamond := rfl

/-! ## The concordance keystone -/

/-- **The house window site is the derived site of the causal order**:
a sieve covers `W` in the landed interior topology iff its pushforward
along the diamond identification covers `toDiamond W` in the derived
topology of `(ℝ, ≤, <)`.  Forward: an interior subdiamond is (by eta and
the definitional iffs) the image of a strictly interior subwindow.
Backward: lift the factorization through the identification and close
under the sieve's downward closure — homs are subsingletons, so the
comparison is free. -/
theorem mem_interiorTopology_iff_derived {W : Window} (S : Sieve W) :
    S ∈ interiorTopology W ↔
      S.functorPushforward windowToDiamond ∈
        diamondTopology (linearOrderKit ℝ) W.toDiamond := by
  constructor
  · intro hS E hle hint
    exact ⟨Window.ofDiamond E,
      homOfLE (Window.ofDiamond_le_iff.mpr hle), 𝟙 E,
      hS (Window.ofDiamond_le_iff.mpr hle)
        (Window.strictlyInterior_ofDiamond_iff.mpr hint),
      Subsingleton.elim _ _⟩
  · intro hS W' hle hint
    obtain ⟨W₀, g, h', hg, -⟩ :=
      hS (Window.le_iff.mp hle) (Window.strictlyInterior_iff.mp hint)
    have hW₀ : W' ≤ W₀ := leOfHom h'
    have hdc := S.downward_closed hg (homOfLE hW₀)
    rwa [Subsingleton.elim (homOfLE hW₀ ≫ g) (homOfLE hle)] at hdc

/-- The book's base site, concordant with the derived site: a window
sieve's pushforward covers the duration `⟨W.len⟩` in the wavy topology
iff its pushforward covers `toDiamond W` in the derived diamond topology
of `(ℝ, ≤, <)` — the landed translation-quotient correspondence composed
with the concordance keystone. -/
theorem wavy_mem_iff_derived {W : Window} (S : Sieve W) :
    S.functorPushforward anchorQuot ∈ wavyTopology ⟨W.len⟩ ↔
      S.functorPushforward windowToDiamond ∈
        diamondTopology (linearOrderKit ℝ) W.toDiamond :=
  (mem_interiorTopology_iff S).symm.trans
    (mem_interiorTopology_iff_derived S)

end

end TTT

end Site

end SuFunctor
