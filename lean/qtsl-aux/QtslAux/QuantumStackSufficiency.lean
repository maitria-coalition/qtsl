import QtslAux.QuantumStackNecessity

/-! # Sufficiency of directedness: the joined two-strand site

`QtslAux.QuantumStackNecessity` refuted the directedness hypothesis of
the attained-regime equivalence
(`descentComparison_isEquivalence_interior`) as droppable: on the
capped stemless V (`Theta`) — where attainment holds and the sieve is
inhabited — essential surjectivity and fullness both fail
(`descentComparison_theta_not_essSurj`,
`descentComparison_theta_not_full`), witnessed by a descent datum
assigning different dimensions to the two interior islands.  This
module is the sufficiency counterpart, on the same site family: modify
the site so that directedness is *restored*, change nothing else, and
the equivalence holds.

* **The joined site.**  `Theta` joins its two strands only at the
  boundary points (`bot`, `top`), where chronological strictness voids
  the joins: no point of the chronological up-set of `bot` lies below
  both strands, so `up_filtered` is unsatisfiable
  (`Theta.no_chronologyKit`), and the ambient interior is two islands
  (`theta_not_interiorDirected`).  `ThetaJoined` moves the joins
  strictly inside the order: a lower trunk (`stem`, a copy of ℚ,
  below both strands), the same two incomparable dense strands, an
  upper trunk (`mid`, a copy of ℚ, above both strands) — and no
  global bottom or top at all.  Each trunk repairs exactly one dead
  field: the stems satisfy `up_filtered` (a common chronological
  successor of points on the two strands — the case that failed at
  `bot`), the mids satisfy `down_directed` (the dual case, which a
  site joined only above would fail the same way).  So the joined
  site carries a full chronology kit
  (`ThetaJoined.chronologyKit`), restoring the descent half of
  bicontinuity whose absence `Vee.no_chronologyKit` established for
  the stemless V and capping could not repair.  The strands
  themselves remain incomparable (`pt_false_not_le_pt_true`):
  restoration is roofs and floors *around* the islands, never
  comparability *of* them.

* **The equivalence, by pure consumption.**  The kit's
  filtered/directed fields are interior directedness
  (`ChronologyKit.interior_directed`), so over the trivial net
  (`thetaJNet` — all of M₁(ℂ) everywhere, attainment `le_rfl`, the
  sieve inhabited, exactly as on `Theta`) the attained-regime
  equivalence applies verbatim:
  `descentComparison_thetaJ_isEquivalence`.  Every hypothesis is
  unchanged from the necessity configuration except directedness, so
  the pair (`descentComparison_theta_not_essSurj`,
  `descentComparison_thetaJ_essSurj`) isolates directedness as the
  exact difference — necessity and sufficiency on one site family.

* **The island contrast.**  On `Theta` the island datum (dimension 1
  on one strand, 2 on the other) was lawful and glued by nothing.  On
  `ThetaJoined` the same two islands sit beneath a common interior
  roof (`islandRoofJ`), and the gluing isomorphisms of *any* descent
  datum tie the island dimensions through it: every datum has equal
  dimensions at the two islands (`thetaJ_datum_island_dim_eq`), so
  the mismatched-dimension datum is not merely glueable now — it is
  unrepresentable (`thetaJ_no_island_datum`) — while everything that
  remains representable *is* glueable (`thetaJ_datum_in_essImage`).
  Dimension data is locally constant along refinements; gluing it
  globally is a connectivity demand on the cover; directedness
  supplies the connectivity.  The necessity module stated that as
  diagnosis; here it is theorem.

Citations: Haag–Kastler, J. Math. Phys. 5, 848 (1964);
Benini–Grant-Stuart–Schenkel, arXiv:2404.14510 (stack conditions);
Martin–Panangaden, arXiv:gr-qc/0407094 (interiority as order-grade
relative compactness).
-/

namespace Qtsl
namespace QuantumStack

open CategoryTheory Matrix DiamondSite QuantumDescent

/-! ## The joined two-strand site -/

/-- The joined two-strand site: a lower trunk (`stem`), two
incomparable dense strands (`pt`), an upper trunk (`mid`).  The two
strands of the capped stemless V, with the joins moved off the
boundary points into the interior of the order — and no global bottom
or top at all. -/
inductive ThetaJoined : Type
  | stem (s : ℚ)
  | pt (s : ℚ) (b : Bool)
  | mid (s : ℚ)

namespace ThetaJoined

/-- Layers ordered `stem < pt < mid` outright; within a layer, by the
rational coordinate (strand points also require the same strand). -/
instance : PartialOrder ThetaJoined where
  le a b :=
    match a, b with
    | .stem s, .stem t => s ≤ t
    | .stem _, .pt _ _ => True
    | .stem _, .mid _ => True
    | .pt s i, .pt t j => i = j ∧ s ≤ t
    | .pt _ _, .mid _ => True
    | .mid s, .mid t => s ≤ t
    | _, _ => False
  le_refl a := by
    cases a with
    | stem s => exact le_rfl
    | pt s b => exact ⟨rfl, le_rfl⟩
    | mid s => exact le_rfl
  le_trans a b c hab hbc := by
    cases a with
    | stem sa =>
      cases b with
      | stem sb =>
        cases c with
        | stem sc => exact hab.trans hbc
        | pt _ _ => trivial
        | mid _ => trivial
      | pt sb bb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => trivial
        | mid _ => trivial
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid _ => trivial
    | pt sa ba =>
      cases b with
      | stem _ => exact hab.elim
      | pt sb bb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt sc bc => exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
        | mid _ => trivial
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid _ => trivial
    | mid sa =>
      cases b with
      | stem _ => exact hab.elim
      | pt _ _ => exact hab.elim
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid sc => exact hab.trans hbc
  le_antisymm a b hab hba := by
    cases a with
    | stem sa =>
      cases b with
      | stem sb => rw [le_antisymm hab hba]
      | pt _ _ => exact hba.elim
      | mid _ => exact hba.elim
    | pt sa ba =>
      cases b with
      | stem _ => exact hab.elim
      | pt sb bb =>
        obtain ⟨hb, hst⟩ := hab
        obtain ⟨-, hts⟩ := hba
        cases hb
        rw [le_antisymm hst hts]
      | mid _ => exact hba.elim
    | mid sa =>
      cases b with
      | stem _ => exact hab.elim
      | pt _ _ => exact hab.elim
      | mid sb => rw [le_antisymm hab hba]

/-- The chronology: strict within each layer (strand points within
their strand), outright across layers upward. -/
def chron : ThetaJoined → ThetaJoined → Prop
  | .stem s, .stem t => s < t
  | .stem _, .pt _ _ => True
  | .stem _, .mid _ => True
  | .pt s i, .pt t j => i = j ∧ s < t
  | .pt _ _, .mid _ => True
  | .mid s, .mid t => s < t
  | _, _ => False

/-- **The descent half, restored**: the joined site carries a full
chronology kit.  `up_filtered` is supplied by the lower trunk (a
common chronological successor for points on the two strands — the
case that is unsatisfiable at `Theta.bot`), `down_directed` by the
upper trunk (the dual case).  Contrast `Theta.no_chronologyKit`:
joining the strands strictly inside the order restores exactly the
structure whose absence the capped V exhibits. -/
def chronologyKit : ChronologyKit ThetaJoined where
  chron := chron
  le_of_chron {a b} h := by
    cases a with
    | stem s =>
      cases b with
      | stem t => exact h.le
      | pt _ _ => trivial
      | mid _ => trivial
    | pt s i =>
      cases b with
      | stem _ => exact h.elim
      | pt t j => exact ⟨h.1, h.2.le⟩
      | mid _ => trivial
    | mid s =>
      cases b with
      | stem _ => exact h.elim
      | pt _ _ => exact h.elim
      | mid t => exact h.le
  chron_of_le_chron {a b c} hab hbc := by
    cases a with
    | stem sa =>
      cases b with
      | stem sb =>
        cases c with
        | stem sc => exact lt_of_le_of_lt hab hbc
        | pt _ _ => trivial
        | mid _ => trivial
      | pt sb bb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => trivial
        | mid _ => trivial
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid _ => trivial
    | pt sa ba =>
      cases b with
      | stem _ => exact hab.elim
      | pt sb bb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt sc bc => exact ⟨hab.1.trans hbc.1, lt_of_le_of_lt hab.2 hbc.2⟩
        | mid _ => trivial
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid _ => trivial
    | mid sa =>
      cases b with
      | stem _ => exact hab.elim
      | pt _ _ => exact hab.elim
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid sc => exact lt_of_le_of_lt hab hbc
  chron_of_chron_le {a b c} hab hbc := by
    cases a with
    | stem sa =>
      cases b with
      | stem sb =>
        cases c with
        | stem sc => exact lt_of_lt_of_le hab hbc
        | pt _ _ => trivial
        | mid _ => trivial
      | pt sb bb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => trivial
        | mid _ => trivial
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid _ => trivial
    | pt sa ba =>
      cases b with
      | stem _ => exact hab.elim
      | pt sb bb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt sc bc => exact ⟨hab.1.trans hbc.1, lt_of_lt_of_le hab.2 hbc.2⟩
        | mid _ => trivial
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid _ => trivial
    | mid sa =>
      cases b with
      | stem _ => exact hab.elim
      | pt _ _ => exact hab.elim
      | mid sb =>
        cases c with
        | stem _ => exact hbc.elim
        | pt _ _ => exact hbc.elim
        | mid sc => exact lt_of_lt_of_le hab hbc
  interpolate {a b} h := by
    cases a with
    | stem s =>
      cases b with
      | stem t =>
        have hst : s < t := h
        exact ⟨.stem ((s + t) / 2), show s < (s + t) / 2 by linarith,
          show (s + t) / 2 < t by linarith⟩
      | pt t j => exact ⟨.stem (s + 1), show s < s + 1 from lt_add_one s,
          trivial⟩
      | mid t => exact ⟨.pt 0 false, trivial, trivial⟩
    | pt s i =>
      cases b with
      | stem _ => exact h.elim
      | pt t j =>
        obtain ⟨hij, hst⟩ := h
        exact ⟨.pt ((s + t) / 2) i, ⟨rfl, by linarith⟩, ⟨hij, by linarith⟩⟩
      | mid t => exact ⟨.pt (s + 1) i, ⟨rfl, by linarith⟩, trivial⟩
    | mid s =>
      cases b with
      | stem _ => exact h.elim
      | pt _ _ => exact h.elim
      | mid t =>
        have hst : s < t := h
        exact ⟨.mid ((s + t) / 2), show s < (s + t) / 2 by linarith,
          show (s + t) / 2 < t by linarith⟩
  up_filtered {a c c'} h h' := by
    cases a with
    | stem s =>
      cases c with
      | stem t =>
        cases c' with
        | stem t' =>
          have h1 : s < t := h
          have h2 : s < t' := h'
          exact ⟨.stem (min t t'), show s < min t t' from lt_min h1 h2,
            show min t t' ≤ t from min_le_left _ _,
            show min t t' ≤ t' from min_le_right _ _⟩
        | pt _ _ => exact ⟨.stem t, h, le_rfl, trivial⟩
        | mid _ => exact ⟨.stem t, h, le_rfl, trivial⟩
      | pt t b =>
        cases c' with
        | stem t' => exact ⟨.stem t', h', trivial, le_rfl⟩
        | pt _ _ => exact ⟨.stem (s + 1), show s < s + 1 from lt_add_one s,
            trivial, trivial⟩
        | mid _ => exact ⟨.stem (s + 1), show s < s + 1 from lt_add_one s,
            trivial, trivial⟩
      | mid t =>
        cases c' with
        | stem t' => exact ⟨.stem t', h', trivial, le_rfl⟩
        | pt _ _ => exact ⟨.stem (s + 1), show s < s + 1 from lt_add_one s,
            trivial, trivial⟩
        | mid _ => exact ⟨.stem (s + 1), show s < s + 1 from lt_add_one s,
            trivial, trivial⟩
    | pt s i =>
      cases c with
      | stem _ => exact h.elim
      | pt t j =>
        cases c' with
        | stem _ => exact h'.elim
        | pt t' j' =>
          exact ⟨.pt (min t t') i, ⟨rfl, lt_min h.2 h'.2⟩,
            ⟨h.1, min_le_left _ _⟩, ⟨h'.1, min_le_right _ _⟩⟩
        | mid _ => exact ⟨.pt t j, h, le_rfl, trivial⟩
      | mid t =>
        cases c' with
        | stem _ => exact h'.elim
        | pt t' j' => exact ⟨.pt t' j', h', trivial, le_rfl⟩
        | mid _ => exact ⟨.pt (s + 1) i, ⟨rfl, by linarith⟩, trivial, trivial⟩
    | mid s =>
      cases c with
      | stem _ => exact h.elim
      | pt _ _ => exact h.elim
      | mid t =>
        cases c' with
        | stem _ => exact h'.elim
        | pt _ _ => exact h'.elim
        | mid t' =>
          have h1 : s < t := h
          have h2 : s < t' := h'
          exact ⟨.mid (min t t'), show s < min t t' from lt_min h1 h2,
            show min t t' ≤ t from min_le_left _ _,
            show min t t' ≤ t' from min_le_right _ _⟩
  down_directed {b d d'} hd hd' := by
    cases b with
    | stem s =>
      cases d with
      | stem t =>
        cases d' with
        | stem t' =>
          have h1 : t < s := hd
          have h2 : t' < s := hd'
          exact ⟨.stem (max t t'), show max t t' < s from max_lt h1 h2,
            show t ≤ max t t' from le_max_left _ _,
            show t' ≤ max t t' from le_max_right _ _⟩
        | pt _ _ => exact hd'.elim
        | mid _ => exact hd'.elim
      | pt _ _ => exact hd.elim
      | mid _ => exact hd.elim
    | pt s j =>
      cases d with
      | stem t =>
        cases d' with
        | stem t' =>
          exact ⟨.stem (max t t'), trivial,
            show t ≤ max t t' from le_max_left _ _,
            show t' ≤ max t t' from le_max_right _ _⟩
        | pt t' i' => exact ⟨.pt t' i', hd', trivial, le_rfl⟩
        | mid _ => exact hd'.elim
      | pt t i =>
        cases d' with
        | stem t' => exact ⟨.pt t i, hd, le_rfl, trivial⟩
        | pt t' i' =>
          exact ⟨.pt (max t t') j, ⟨rfl, max_lt hd.2 hd'.2⟩,
            ⟨hd.1, le_max_left _ _⟩, ⟨hd'.1, le_max_right _ _⟩⟩
        | mid _ => exact hd'.elim
      | mid _ => exact hd.elim
    | mid s =>
      cases d with
      | stem t =>
        cases d' with
        | stem t' => exact ⟨.mid (s - 1),
            show s - 1 < s from sub_one_lt s, trivial, trivial⟩
        | pt t' i' => exact ⟨.mid (s - 1),
            show s - 1 < s from sub_one_lt s, trivial, trivial⟩
        | mid t' => exact ⟨.mid t', hd', trivial, le_rfl⟩
      | pt t i =>
        cases d' with
        | stem t' => exact ⟨.mid (s - 1),
            show s - 1 < s from sub_one_lt s, trivial, trivial⟩
        | pt t' i' => exact ⟨.mid (s - 1),
            show s - 1 < s from sub_one_lt s, trivial, trivial⟩
        | mid t' => exact ⟨.mid t', hd', trivial, le_rfl⟩
      | mid t =>
        cases d' with
        | stem t' => exact ⟨.mid t, hd, le_rfl, trivial⟩
        | pt t' i' => exact ⟨.mid t, hd, le_rfl, trivial⟩
        | mid t' =>
          have h1 : t < s := hd
          have h2 : t' < s := hd'
          exact ⟨.mid (max t t'), show max t t' < s from max_lt h1 h2,
            show t ≤ max t t' from le_max_left _ _,
            show t' ≤ max t t' from le_max_right _ _⟩

/-- The strands remain incomparable after the joins: the `false`
strand does not sit below the `true` strand. -/
theorem pt_false_not_le_pt_true :
    ¬ ((ThetaJoined.pt 0 false : ThetaJoined) ≤ .pt 0 true) :=
  fun h => Bool.false_ne_true h.1

/-- The strands remain incomparable after the joins: the `true` strand
does not sit below the `false` strand. -/
theorem pt_true_not_le_pt_false :
    ¬ ((ThetaJoined.pt 0 true : ThetaJoined) ≤ .pt 0 false) :=
  fun h => Bool.false_ne_true h.1.symm

end ThetaJoined

/-! ## The ambient diamond, the islands, and the roof -/

/-- The ambient diamond of the joined site: trunk point to trunk
point. -/
def thetaJD : Diamond ThetaJoined := ⟨.stem 0, .mid 0, trivial⟩

/-- The degenerate diamond on the `false` strand — the same island
geometry as on the capped V. -/
def leftIslandJ : Diamond ThetaJoined := ⟨.pt 0 false, .pt 0 false, le_rfl⟩

/-- The degenerate diamond on the `true` strand. -/
def rightIslandJ : Diamond ThetaJoined := ⟨.pt 0 true, .pt 0 true, le_rfl⟩

theorem leftIslandJ_interior :
    ThetaJoined.chronologyKit.toMixingKit.interiorMem thetaJD leftIslandJ :=
  ⟨trivial, trivial⟩

theorem rightIslandJ_interior :
    ThetaJoined.chronologyKit.toMixingKit.interiorMem thetaJD rightIslandJ :=
  ⟨trivial, trivial⟩

theorem leftIslandJ_le : leftIslandJ ≤ thetaJD := ⟨trivial, trivial⟩

theorem rightIslandJ_le : rightIslandJ ≤ thetaJD := ⟨trivial, trivial⟩

theorem leftIslandJ_arrow :
    (interiorSieve ThetaJoined.chronologyKit.toMixingKit thetaJD).arrows
      (homOfLE leftIslandJ_le) :=
  ⟨leftIslandJ, leftIslandJ_interior, le_rfl⟩

theorem rightIslandJ_arrow :
    (interiorSieve ThetaJoined.chronologyKit.toMixingKit thetaJD).arrows
      (homOfLE rightIslandJ_le) :=
  ⟨rightIslandJ, rightIslandJ_interior, le_rfl⟩

/-- **The roof**: an interior diamond containing both islands — lower
endpoint on the lower trunk, upper endpoint on the upper trunk.  On
the capped V no such member exists (its interior members live in a
single strand, `theta_member_shape`); the roof is what the joins
buy. -/
def islandRoofJ : Diamond ThetaJoined := ⟨.stem 1, .mid (-1), trivial⟩

theorem islandRoofJ_interior :
    ThetaJoined.chronologyKit.toMixingKit.interiorMem thetaJD islandRoofJ :=
  ⟨show (0 : ℚ) < 1 by norm_num, show (-1 : ℚ) < 0 by norm_num⟩

theorem islandRoofJ_le : islandRoofJ ≤ thetaJD :=
  ⟨show (0 : ℚ) ≤ 1 by norm_num, show (-1 : ℚ) ≤ 0 by norm_num⟩

theorem islandRoofJ_arrow :
    (interiorSieve ThetaJoined.chronologyKit.toMixingKit thetaJD).arrows
      (homOfLE islandRoofJ_le) :=
  ⟨islandRoofJ, islandRoofJ_interior, le_rfl⟩

theorem leftIslandJ_le_roof : leftIslandJ ≤ islandRoofJ := ⟨trivial, trivial⟩

theorem rightIslandJ_le_roof : rightIslandJ ≤ islandRoofJ :=
  ⟨trivial, trivial⟩

/-! ## The trivial net -/

/-- The trivial net on the joined site: every diamond carries all of
M₁(ℂ) — the same net shape as on the capped V, so attainment holds and
the sieve is inhabited, and the only hypothesis that changed between
the two sites is directedness. -/
noncomputable def thetaJNet : ObservableNet ThetaJoined (Fin 1) where
  alg _ := ⊤
  isotone _ := le_rfl

theorem thetaJNet_attained :
    thetaJNet.alg thetaJD ≤ thetaJNet.alg leftIslandJ :=
  le_rfl

/-! ## Directedness restored, and the equivalence -/

/-- **The interior of the joined site's ambient diamond is directed**
— by the landed general lemma, consuming the restored kit's
filtered/directed fields.  Contrast `theta_not_interiorDirected`. -/
theorem thetaJ_interiorDirected :
    InteriorDirected ThetaJoined.chronologyKit.toMixingKit thetaJD :=
  ThetaJoined.chronologyKit.interior_directed thetaJD

/-- **The attained-regime equivalence holds on the joined site**: with
directedness restored — and every other hypothesis exactly as in the
two-island refutation — the descent comparison at the canonical
interior cover is an equivalence.  Together with
`descentComparison_theta_not_essSurj` this pair isolates directedness
as the exact difference: necessity and sufficiency on one site
family. -/
theorem descentComparison_thetaJ_isEquivalence :
    (descentComparison thetaJNet thetaJD
      (interiorSieve ThetaJoined.chronologyKit.toMixingKit
        thetaJD)).IsEquivalence :=
  descentComparison_isEquivalence_interior _ thetaJNet leftIslandJ_interior
    le_rfl (ThetaJoined.chronologyKit.interior_directed thetaJD)

/-- Essential surjectivity on the joined site — the sufficiency twin
of `descentComparison_theta_not_essSurj`. -/
theorem descentComparison_thetaJ_essSurj :
    (descentComparison thetaJNet thetaJD
      (interiorSieve ThetaJoined.chronologyKit.toMixingKit
        thetaJD)).EssSurj :=
  descentComparison_thetaJ_isEquivalence.essSurj

/-- Fullness on the joined site — the sufficiency twin of
`descentComparison_theta_not_full`. -/
theorem descentComparison_thetaJ_full :
    (descentComparison thetaJNet thetaJD
      (interiorSieve ThetaJoined.chronologyKit.toMixingKit
        thetaJD)).Full :=
  descentComparison_thetaJ_isEquivalence.full

/-- **Every descent datum on the joined site is glueable**: the
statement-shape twin, negation removed, of
`islandDatum_not_in_essImage`. -/
theorem thetaJ_datum_in_essImage
    (Xd : DescentDatum thetaJNet thetaJD
      (interiorSieve ThetaJoined.chronologyKit.toMixingKit thetaJD)) :
    ∃ ρ : FinRep ↥(thetaJNet.alg thetaJD),
      Nonempty ((descentComparison thetaJNet thetaJD
        (interiorSieve ThetaJoined.chronologyKit.toMixingKit
          thetaJD)).obj ρ ≅ Xd) :=
  descentComparison_thetaJ_essSurj.mem_essImage Xd

/-! ## The island contrast: dimension data is tied through the roof -/

/-- **Any descent datum has equal dimensions at the two islands**: the
gluing isomorphisms into the roof tie both island components to the
roof component.  On the capped V, where no roof exists, `islandDatum`
assigns dimensions 1 and 2; here that mismatch is unrepresentable. -/
theorem thetaJ_datum_island_dim_eq
    (Xd : DescentDatum thetaJNet thetaJD
      (interiorSieve ThetaJoined.chronologyKit.toMixingKit thetaJD)) :
    (Xd.obj leftIslandJ_le leftIslandJ_arrow).dim
      = (Xd.obj rightIslandJ_le rightIslandJ_arrow).dim := by
  have hL := FinRep.dim_eq_of_iso
    (Xd.glue leftIslandJ_le_roof islandRoofJ_le islandRoofJ_arrow
      leftIslandJ_arrow)
  have hR := FinRep.dim_eq_of_iso
    (Xd.glue rightIslandJ_le_roof islandRoofJ_le islandRoofJ_arrow
      rightIslandJ_arrow)
  exact hL.trans hR.symm

/-- **The mismatched island datum is unrepresentable on the joined
site**: no descent datum assigns dimension 1 to one island and 2 to
the other — the exact assignment that is lawful (and glued by
nothing) on the capped V. -/
theorem thetaJ_no_island_datum :
    ¬ ∃ Xd : DescentDatum thetaJNet thetaJD
      (interiorSieve ThetaJoined.chronologyKit.toMixingKit thetaJD),
      (Xd.obj leftIslandJ_le leftIslandJ_arrow).dim = 1 ∧
      (Xd.obj rightIslandJ_le rightIslandJ_arrow).dim = 2 := by
  rintro ⟨Xd, h1, h2⟩
  have h := thetaJ_datum_island_dim_eq Xd
  rw [h1, h2] at h
  exact absurd h (by decide)

end QuantumStack
end Qtsl

-- Axiom receipts (expected: subsets of [propext, Classical.choice, Quot.sound])
#print axioms Qtsl.QuantumStack.ThetaJoined.chronologyKit
#print axioms Qtsl.QuantumStack.ThetaJoined.pt_false_not_le_pt_true
#print axioms Qtsl.QuantumStack.ThetaJoined.pt_true_not_le_pt_false
#print axioms Qtsl.QuantumStack.leftIslandJ_interior
#print axioms Qtsl.QuantumStack.islandRoofJ_interior
#print axioms Qtsl.QuantumStack.thetaJNet_attained
#print axioms Qtsl.QuantumStack.thetaJ_interiorDirected
#print axioms Qtsl.QuantumStack.descentComparison_thetaJ_isEquivalence
#print axioms Qtsl.QuantumStack.descentComparison_thetaJ_essSurj
#print axioms Qtsl.QuantumStack.descentComparison_thetaJ_full
#print axioms Qtsl.QuantumStack.thetaJ_datum_in_essImage
#print axioms Qtsl.QuantumStack.thetaJ_datum_island_dim_eq
#print axioms Qtsl.QuantumStack.thetaJ_no_island_datum
