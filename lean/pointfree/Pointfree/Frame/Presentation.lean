import Mathlib.Order.Nucleus
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Hom
import Mathlib.Order.UpperLower.Principal

/-! # Frames presented by generators and relations

A frame presentation, assembled from stock parts.  Generators form a
meet-semilattice `A` (so that finite meets of generators are again
generators — the hit-and-miss data of the hyperspace presentation are
the motivating case); relations are inequalities between elements of
the **free frame** on `A`.

* The free frame on a meet-semilattice is its lower-set lattice
  `LowerSet A` (Johnstone, *Stone Spaces* II.1.2): joins are unions,
  finite meets are intersections, and `LowerSet.Iic` embeds `A`
  preserving finite meets.
* A relation set `R` is forced by the **least nucleus** `j` with
  `a ≤ j b` for every `(a, b) ∈ R`; the nuclei on a frame form a
  complete lattice with pointwise infima, so the least forcing nucleus
  is an infimum, not a transfinite construction.
* The presented frame is the range of that nucleus, with the frame
  structure and the quotient map `Nucleus.restrict` supplied by
  mathlib.

Because the generators enter through `LowerSet.Iic` and the quotient
map is a frame homomorphism, three interface facts cost nothing and
hold for **every** relation set: the generator map preserves finite
meets and the top, and its image join-generates the presented frame.
The relations themselves hold by construction (`restrict_rel_le`).
Frame homomorphisms out of the presented frame are determined by
their generator values (`hom_ext`); the analogous determination
theorem for continuous *valuations* — where modularity replaces the
homomorphism property on the join side — is
`Pointfree.Valuation.ext_of_generators`.
-/

namespace Pointfree

open LowerSet

variable {A : Type*} [SemilatticeInf A]

/-- The least nucleus on the free frame `LowerSet A` forcing every
relation in `R`: for `(a, b) ∈ R` the quotient satisfies `a ≤ b`.
Nuclei have pointwise infima, so the forcing conditions survive the
`sInf` and the least forcing nucleus exists by construction. -/
def presentingNucleus (R : Set (LowerSet A × LowerSet A)) : Nucleus (LowerSet A) :=
  sInf {j | ∀ r ∈ R, r.1 ≤ j r.2}

theorem le_presentingNucleus_of_mem {R : Set (LowerSet A × LowerSet A)}
    {r : LowerSet A × LowerSet A} (hr : r ∈ R) :
    r.1 ≤ presentingNucleus R r.2 := by
  rw [presentingNucleus, Nucleus.sInf_apply]
  exact le_iInf₂ fun j hj => hj r hr

/-- The frame presented by the generator semilattice `A` and the
relation set `R`: the range of the least forcing nucleus, with the
frame structure mathlib installs on the range of any nucleus. -/
abbrev Presented (R : Set (LowerSet A × LowerSet A)) : Set (LowerSet A) :=
  Set.range (presentingNucleus R)

variable (R : Set (LowerSet A × LowerSet A))

/-- The generator map: a generator `p : A` lands in the presented
frame as the image of its principal lower set under the quotient. -/
def gen (p : A) : Presented R :=
  (presentingNucleus R).restrict (Iic p)

/-- Generators meet as in `A`: the presented frame's finite meets of
generators are again generators, for every relation set — `Iic`
preserves meets and the quotient is a frame homomorphism, so no
relation is spent on it. -/
theorem gen_inf (p q : A) : gen R (p ⊓ q) = gen R p ⊓ gen R q := by
  simp only [gen, Iic_inf, map_inf]

/-- The empty generator datum is the top of the presented frame. -/
theorem gen_top [OrderTop A] : gen R ⊤ = ⊤ := by
  have h : (Iic (⊤ : A)) = (⊤ : LowerSet A) := by
    ext a
    simp
  simp only [gen, h, map_top]

theorem gen_mono : Monotone (gen R) := fun _ _ hpq =>
  OrderHomClass.mono ((presentingNucleus R).restrict)
    (Iic_le.mpr (mem_Iic_iff.mpr hpq))

/-- The relations hold in the presented frame: forcing, then
idempotence. -/
theorem restrict_rel_le {r : LowerSet A × LowerSet A} (hr : r ∈ R) :
    (presentingNucleus R).restrict r.1 ≤ (presentingNucleus R).restrict r.2 := by
  rw [← Subtype.coe_le_coe]
  show presentingNucleus R r.1 ≤ presentingNucleus R r.2
  simpa using (presentingNucleus R).monotone (le_presentingNucleus_of_mem hr)

/-- **Join-generation**: every element of the presented frame is the
join of the generators arising from its own underlying lower set —
for every relation set.  (The decomposition of a lower set into
principal lower sets, pushed through the quotient homomorphism.) -/
theorem eq_iSup_gen (x : Presented R) :
    x = ⨆ p ∈ (x : LowerSet A), gen R p := by
  have hdecomp : (x : LowerSet A) = ⨆ p ∈ (x : LowerSet A), Iic p := by
    apply SetLike.coe_injective
    rw [LowerSet.coe_iSup₂]
    ext a
    simp only [SetLike.mem_coe, Set.mem_iUnion, LowerSet.coe_Iic, Set.mem_Iic]
    exact ⟨fun ha => ⟨a, ha, le_rfl⟩,
      fun ⟨p, hp, hap⟩ => (x : LowerSet A).lower hap hp⟩
  conv_lhs => rw [← (presentingNucleus R).giRestrict.l_u_eq x, hdecomp]
  rw [map_iSup₂]
  rfl

/-- Frame homomorphisms out of a presented frame are determined by
their generator values. -/
theorem hom_ext {M : Type*} [Order.Frame M] {f g : FrameHom (Presented R) M}
    (h : ∀ p, f (gen R p) = g (gen R p)) : f = g := by
  ext x
  rw [eq_iSup_gen R x, map_iSup₂, map_iSup₂]
  exact biSup_congr fun p _ => h p

end Pointfree
