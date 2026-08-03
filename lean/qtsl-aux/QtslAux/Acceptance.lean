import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice

/-! # Soundness of acyclic citation towers

This module proves that a tower of certificate rows with acyclic citations is
sound. A `Row` is either a base fact (`Row.base`) or an inference (`Row.ext`)
that cites a list of earlier rows as premises and asserts a conclusion. The
relation `cites C j i` holds when row `i` cites row `j`, and `Acyclic C` says
no row transitively cites itself.

Main results:

* `acyclic_wellFounded`: over a finite index type, an acyclic citation
  relation is well-founded.
* `towerCitation_sound` (and the well-foundedness-parametrized variant
  `towerCitation_sound_of_wf`): if every base row is true, every side
  condition holds, and each inference row's conclusion follows from the truth
  of its cited premises, then every row of the tower holds.
* `towerCitation_root`: the semantic truth of any conclusion appearing as the
  conclusion of some row in a sound tower.
* `citePos_sound`, `citeCmpl_sound`: citing a subset `R ⊆ D` transfers a
  monotone predicate from `R` to `D`, and an antitone predicate from `Rᶜ` to
  `Dᶜ` — the two ways one certified region may cite another.
-/

namespace Qtsl.Acceptance

variable {σ J ι : Type*}

inductive Row (σ J ι : Type*) where
  | base (s : σ)
  | ext (prems : List ι) (concl : J)

def Row.cited : Row σ J ι → List ι
  | .base _ => []
  | .ext prems _ => prems

def Row.holds (baseTrue : σ → Prop) (sem : J → Prop) : Row σ J ι → Prop
  | .base s => baseTrue s
  | .ext _ concl => sem concl

def cites (C : ι → Row σ J ι) (j i : ι) : Prop :=
  j ∈ (C i).cited

def Acyclic (C : ι → Row σ J ι) : Prop :=
  ∀ i, ¬ Relation.TransGen (cites C) i i

theorem acyclic_wellFounded [Finite ι] (C : ι → Row σ J ι)
    (hacyc : Acyclic C) : WellFounded (cites C) := by
  haveI : Std.Irrefl (Relation.TransGen (cites C)) := ⟨hacyc⟩
  exact Subrelation.wf (fun {_ _} h => Relation.TransGen.single h)
    (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen (cites C)))

theorem towerCitation_sound_of_wf
    (C : ι → Row σ J ι) (baseTrue : σ → Prop) (sem : J → Prop)
    (SideOK : ι → Prop)
    (hbase : ∀ i s, C i = Row.base s → baseTrue s)
    (hside : ∀ i, SideOK i)
    (hstep : ∀ i prems concl, C i = Row.ext prems concl → SideOK i →
      (∀ j ∈ prems, Row.holds baseTrue sem (C j)) → sem concl)
    (hwf : WellFounded (cites C)) :
    ∀ i, Row.holds baseTrue sem (C i) := by
  intro i
  refine hwf.induction (C := fun k => Row.holds baseTrue sem (C k)) i
    (fun x ih => ?_)
  cases hCx : C x with
  | base s => exact hbase x s hCx
  | ext prems concl =>
    exact hstep x prems concl hCx (hside x) fun j hj =>
      ih j (by unfold cites; rw [hCx]; exact hj)

theorem towerCitation_sound [Finite ι]
    (C : ι → Row σ J ι) (baseTrue : σ → Prop) (sem : J → Prop)
    (SideOK : ι → Prop)
    (hbase : ∀ i s, C i = Row.base s → baseTrue s)
    (hside : ∀ i, SideOK i)
    (hstep : ∀ i prems concl, C i = Row.ext prems concl → SideOK i →
      (∀ j ∈ prems, Row.holds baseTrue sem (C j)) → sem concl)
    (hacyc : Acyclic C) :
    ∀ i, Row.holds baseTrue sem (C i) :=
  towerCitation_sound_of_wf C baseTrue sem SideOK hbase hside hstep
    (acyclic_wellFounded C hacyc)

theorem towerCitation_root [Finite ι]
    (C : ι → Row σ J ι) (baseTrue : σ → Prop) (sem : J → Prop)
    (SideOK : ι → Prop)
    (hbase : ∀ i s, C i = Row.base s → baseTrue s)
    (hside : ∀ i, SideOK i)
    (hstep : ∀ i prems concl, C i = Row.ext prems concl → SideOK i →
      (∀ j ∈ prems, Row.holds baseTrue sem (C j)) → sem concl)
    (hacyc : Acyclic C)
    {Jroot : J} (hroot : ∃ i prems, C i = Row.ext prems Jroot) :
    sem Jroot := by
  obtain ⟨i, prems, hCi⟩ := hroot
  have h := towerCitation_sound C baseTrue sem SideOK hbase hside hstep hacyc i
  rw [hCi] at h
  exact h

theorem citePos_sound {X : Type*} {R D : Set X} {P : Set X → Prop}
    (hmono : Monotone P) (hsub : R ⊆ D) (hR : P R) : P D :=
  hmono hsub hR

theorem citeCmpl_subset {X : Type*} {R D : Set X} (hsub : R ⊆ D) :
    Dᶜ ⊆ Rᶜ :=
  fun _x hxD hxR => hxD (hsub hxR)

theorem citeCmpl_sound {X : Type*} {R D : Set X} {P : Set X → Prop}
    (hanti : Antitone P) (hsub : R ⊆ D) (hR : P Rᶜ) : P Dᶜ :=
  hanti (citeCmpl_subset hsub) hR

end Qtsl.Acceptance

#print axioms Qtsl.Acceptance.acyclic_wellFounded
#print axioms Qtsl.Acceptance.towerCitation_sound_of_wf
#print axioms Qtsl.Acceptance.towerCitation_sound
#print axioms Qtsl.Acceptance.towerCitation_root
#print axioms Qtsl.Acceptance.citePos_sound
#print axioms Qtsl.Acceptance.citeCmpl_subset
#print axioms Qtsl.Acceptance.citeCmpl_sound
