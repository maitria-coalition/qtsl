import SuFunctor.Adequacy.Pde

/-! # Adequacy: declared-data presentations of PDE and SPDE mechanisms

The PDE module proves the adequacy square for every
differential-polynomial mechanism, with the mechanism given as a Lean
value (`PdeMechanism`).  A *presented* system, however, arrives as
declared row data: a list of state variables, a list of jet-variable
declarations (base field variable × spatial derivative order), and
per-component drift polynomials as sparse exponent-tuple rows over the
positional index space `state ++ jets`.  This module deep-embeds that
row form and mechanizes the **compile edge** from declared data into
the formation rule's mechanism:

* `PdeRowSpec` — the row form: state variables, jet declarations,
  sparse drift rows; `PdeRowSpec.toMechanism` — the compile.
* The positional convention is the producer surface's: positions below
  `stateVars.length` denote field components at derivative order zero;
  later positions denote the declared jets, in order.  `toMv_congr`
  shows the compile reads no position beyond a row's width, so the
  out-of-range fallback of `bind` is inert on well-formed data
  (`toMechanism_congr_inhabited`).
* Instance ties: the heat, viscous-Burgers, Fisher–KPP, and
  cross-coupled mechanisms are re-derived **from declared rows** —
  `heatRowSpec_toMechanism` etc. are polynomial identities between the
  compiled data and the hand-written mechanisms, so the adequacy
  squares and the semantic-universe wiring specialize to declared data
  with no new proof (`heat_rows_adequacy`, `su_pde_rows_adequacy`),
  and the heat module's hard-coded rows are the rows of the declared
  data (`heatAt_iff_rowsAt`).

The stochastic complement embeds the noise-spectrum declaration of the
SPDE profile: finitely many driver rows (spatial shapes as
exact-rational combinations of the domain's **orthonormal** Fourier
basis, constant amplitudes at this stratum) and a **required** tail
form in exactly one of three shapes — `zero`, a rational trace
`bracket`, or declared-`divergent`.  Absence of a tail is
unrepresentable here (the field is not optional), mirroring the schema
stratum, and the derived covariance data is computed, never stored:

* `SpectrumDecl.explicitTrace` — the explicit part of the covariance
  trace by Parseval on the orthonormal basis, exact in `ℚ`, with
  coefficients **grouped per basis element** before squaring
  (duplicate declarations of one element sum rather than double-count
  — `dupSpec_grouping` is the witness) and `sin` at mode 0 massless
  (`sin0_massless`).
* `SpectrumDecl.qDiag` — the derived diagonal (the q-table read);
  `explicitTrace_eq_sum_qDiag` — the trace is the sum of the diagonal
  over the spectrum's support (off-diagonal entries never enter a
  trace).
* `SpectrumDecl.plainTrace` — the plain-trace consumer seam:
  total-or-refusing, with the `divergent` arm **structurally refused**
  (`plainTrace_divergent_none`) — a declared-divergent tail has no
  plain trace, and no consumer defaults it to zero.
* The certified stochastic-heat spectrum (`heatSpectrum`: five drivers
  realizing `q₁ = 1/5`, `q₂ = 3/50` as sums of rational squares, tail
  zero) with its derived trace `13/50`, its q-table entries, and the
  floor identity `(13/50) / (2·(1/10)) = 13/10` — the declared data of
  the certified instance, recomputed by theorem.

**Named obligations, staged (not proven here)**: the analytic tie from
a formal spectrum to the covariance operator of a Q-Wiener process
(Parseval/orthonormality on the function space — constructor-side);
the Fourier mode-projection semantics tying a declared jet drift to
its mode flow (the compile-for-semantics leg); non-constant
(multiplicative) amplitude columns; spatial dimension ≥ 2 for the
mechanized square (the declaration form carries multi-indices; the
mesh square is one-dimensional in space, its own recorded fence);
noise-field kernels beyond finite declared spectra. -/

namespace SuFunctor
namespace Adequacy

open CategoryTheory PseudoDoubleCategoryStruct

/-! ## The row form and the compile edge -/

/-- One sparse drift-row term: an exact-rational coefficient and a
positional exponent tuple over the index space `state ++ jets`
(position `p` carries exponent `exps[p]`; positions beyond the tuple's
length are unused). -/
structure RowTerm where
  /-- The exact-rational coefficient. -/
  coeff : ℚ
  /-- The positional exponent tuple. -/
  exps : List ℕ

/-- A declared PDE row specification: the state variables (field
components, each also naming a derivative-order-zero position), the
declared jet variables (component × spatial order, order bounded by
`k` at the type), and per-component sparse drift rows. -/
structure PdeRowSpec (ι : Type) (k : ℕ) where
  /-- Field components, in positional order (the variable-name list). -/
  stateVars : List ι
  /-- Declared jet variables, in positional order after the state
  variables. -/
  jets : List (ι × Fin (k + 1))
  /-- Per-component drift rows over the positional index space. -/
  drift : ι → List RowTerm

namespace PdeRowSpec

variable {ι : Type} {k : ℕ}

/-- Well-formedness of a row specification: every drift term's
exponent tuple fits inside the declared index space.  Data and gate
are deliberately separate — the gate is admission, never a
constructor field. -/
def WF (S : PdeRowSpec ι k) : Prop :=
  ∀ i : ι, ∀ t ∈ S.drift i, t.exps.length ≤ S.stateVars.length + S.jets.length

/-- The positional binding of the index space `state ++ jets`:
positions below `stateVars.length` read a field component at
derivative order zero; later positions read the declared jets.  The
fallback value is inert on well-formed data
(`toMechanism_congr_inhabited`). -/
def bind [Inhabited ι] (S : PdeRowSpec ι k) (p : ℕ) : ι × Fin (k + 1) :=
  if p < S.stateVars.length then
    (S.stateVars.getD p default, ⟨0, Nat.succ_pos k⟩)
  else
    S.jets.getD (p - S.stateVars.length) (default, ⟨0, Nat.succ_pos k⟩)

end PdeRowSpec

/-- The monomial of one exponent tuple, read from position `p`
onward: `∏ⱼ X (b (p+j)) ^ exps[j]`. -/
noncomputable def termProd {σ : Type} (b : ℕ → σ) :
    ℕ → List ℕ → MvPolynomial σ ℝ
  | _, [] => 1
  | p, e :: es => MvPolynomial.X (b p) ^ e * termProd b (p + 1) es

/-- The polynomial of a sparse row list under a positional binding. -/
noncomputable def toMv {σ : Type} (b : ℕ → σ) : List RowTerm → MvPolynomial σ ℝ
  | [] => 0
  | t :: ts => MvPolynomial.C (t.coeff : ℝ) * termProd b 0 t.exps + toMv b ts

/-- The monomial reads no position at or beyond `p + es.length`:
bindings agreeing below a tuple's width produce the same monomial. -/
theorem termProd_congr {σ : Type} {b₁ b₂ : ℕ → σ} :
    ∀ (p : ℕ) (es : List ℕ),
      (∀ j, j < es.length → b₁ (p + j) = b₂ (p + j)) →
      termProd b₁ p es = termProd b₂ p es
  | _, [], _ => rfl
  | p, e :: es, h => by
    have h0 : b₁ p = b₂ p := by
      simpa using h 0 (by simp only [List.length_cons]; omega)
    have hrest : ∀ j, j < es.length → b₁ (p + 1 + j) = b₂ (p + 1 + j) := by
      intro j hj
      have h' := h (j + 1) (by simp only [List.length_cons]; omega)
      simpa [show p + (j + 1) = p + 1 + j by omega] using h'
    simp [termProd, h0, termProd_congr (p + 1) es hrest]

/-- The compile reads no position beyond a row's width. -/
theorem toMv_congr {σ : Type} {b₁ b₂ : ℕ → σ} :
    ∀ rows : List RowTerm,
      (∀ t ∈ rows, ∀ j, j < t.exps.length → b₁ j = b₂ j) →
      toMv b₁ rows = toMv b₂ rows
  | [], _ => rfl
  | t :: ts, h => by
    have hterm : termProd b₁ 0 t.exps = termProd b₂ 0 t.exps :=
      termProd_congr 0 t.exps fun j hj => by
        simpa using h t (List.mem_cons_self ..) j hj
    have hrest : toMv b₁ ts = toMv b₂ ts :=
      toMv_congr ts fun u hu => h u (List.mem_cons_of_mem _ hu)
    simp [toMv, hterm, hrest]

namespace PdeRowSpec

variable {ι : Type} {k : ℕ}

/-- **The compile edge**: declared row data to the formation rule's
differential-polynomial mechanism. -/
noncomputable def toMechanism [Inhabited ι] (S : PdeRowSpec ι k) :
    PdeMechanism ι k where
  drift i := toMv S.bind (S.drift i)

/-- On well-formed data the compile never reads `bind`'s fallback: the
compiled mechanism does not depend on the choice of default element.
(The junk arm of the positional binding is unreachable — congruence,
not convention.) -/
theorem toMechanism_congr_inhabited (S : PdeRowSpec ι k) (hWF : S.WF)
    (d₁ d₂ : Inhabited ι) :
    @toMechanism ι k d₁ S = @toMechanism ι k d₂ S := by
  have hdrift : ∀ i : ι,
      toMv (@bind ι k d₁ S) (S.drift i) = toMv (@bind ι k d₂ S) (S.drift i) := by
    intro i
    refine toMv_congr (S.drift i) fun t ht j hj => ?_
    have hjlt : j < S.stateVars.length + S.jets.length :=
      lt_of_lt_of_le hj (hWF i t ht)
    by_cases hs : j < S.stateVars.length
    · simp only [bind, if_pos hs, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hs, Option.getD_some]
    · have hjj : j - S.stateVars.length < S.jets.length := by omega
      simp only [bind, if_neg hs, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hjj, Option.getD_some]
  cases d₁; cases d₂
  simp only [toMechanism, PdeMechanism.mk.injEq]
  funext i
  exact hdrift i

end PdeRowSpec

/-! ## Instance ties: the certified mechanisms from declared rows

Each tie is a polynomial identity between compiled declared data and
the hand-written mechanism of the PDE module; the squares then
specialize with no new proof.  Coefficients are declared exact-rational
and include along the canonical ring morphism. -/

section InstanceTies

/-- Heat as declared rows: one field component, one declared jet
(`∂²ₓu`), drift `c · u_xx` as the single sparse row `[0, 1]`. -/
def heatRowSpec (c : ℚ) : PdeRowSpec PUnit 2 where
  stateVars := [()]
  jets := [((), ⟨2, by norm_num⟩)]
  drift _ := [⟨c, [0, 1]⟩]

/-- The declared heat rows compile to the heat mechanism. -/
theorem heatRowSpec_toMechanism (c : ℚ) :
    (heatRowSpec c).toMechanism = heatMechanism (c : ℝ) := by
  simp only [PdeRowSpec.toMechanism, heatMechanism, PdeMechanism.mk.injEq]
  funext i
  norm_num [heatRowSpec, toMv, termProd, PdeRowSpec.bind,
    List.getD_cons_zero, List.getD_cons_succ]

/-- The heat module's hard-coded rows are the rows of the declared
data: the pointwise tie, transported through the compile edge. -/
theorem heatAt_iff_rowsAt {c : ℚ} {u : ℝ → ℝ → ℝ} {x t : ℝ} :
    HeatAt (c : ℝ) u x t ↔
      PdeAt ((heatRowSpec c).toMechanism) (fun y s _ => u y s) x t := by
  rw [heatRowSpec_toMechanism]
  exact heatAt_iff_pdeAt

/-- **The heat adequacy square from declared data**: compiling the
cyclic mesh of the declared heat rows and denoting agrees with
interpreting globally — one line at the frame square, with the
mechanism produced by the compile edge rather than written by hand. -/
theorem heat_rows_adequacy (c : ℚ) (M : RingMesh) {T : Set ℝ}
    (hT : IsOpen T) {a : Crd (HeatRec (PUnit → ℝ))} :
    ∃ α : Cell
        (looseConj (((heatRowSpec c).toMechanism).rows.meshAtoms M T) : Loose a a)
        (suppC (((heatRowSpec c).toMechanism).rows.classicalRecs M T))
        (𝟙 a) (𝟙 a),
      Cell.IsInvertible α :=
  pde_adequacy ((heatRowSpec c).toMechanism) M hT

/-- Viscous Burgers as declared rows: jets `∂ₓu`, `∂²ₓu`; drift
`c·u_xx − u·u_x` as two sparse rows. -/
def burgersRowSpec (c : ℚ) : PdeRowSpec PUnit 2 where
  stateVars := [()]
  jets := [((), ⟨1, by norm_num⟩), ((), ⟨2, by norm_num⟩)]
  drift _ := [⟨c, [0, 0, 1]⟩, ⟨-1, [1, 1, 0]⟩]

/-- The declared Burgers rows compile to the Burgers mechanism. -/
theorem burgersRowSpec_toMechanism (c : ℚ) :
    (burgersRowSpec c).toMechanism = burgersMechanism (c : ℝ) := by
  simp only [PdeRowSpec.toMechanism, burgersMechanism, PdeMechanism.mk.injEq]
  funext i
  norm_num [burgersRowSpec, toMv, termProd, PdeRowSpec.bind,
    List.getD_cons_zero, List.getD_cons_succ, map_neg, map_one]
  try push_cast
  try ring

/-- Fisher–KPP as declared rows, in canonical expanded form
(`u_xx + u − u²`); the tie to the factored mechanism
(`u_xx + u·(1 − u)`) is a ring identity — declared canonical data and
human-factored presentation compile to one polynomial. -/
def kppRowSpec : PdeRowSpec PUnit 2 where
  stateVars := [()]
  jets := [((), ⟨1, by norm_num⟩), ((), ⟨2, by norm_num⟩)]
  drift _ := [⟨1, [0, 0, 1]⟩, ⟨1, [1, 0, 0]⟩, ⟨-1, [2, 0, 0]⟩]

/-- The declared KPP rows compile to the KPP mechanism. -/
theorem kppRowSpec_toMechanism :
    kppRowSpec.toMechanism = kppMechanism := by
  simp only [PdeRowSpec.toMechanism, kppMechanism, PdeMechanism.mk.injEq]
  funext i
  norm_num [kppRowSpec, toMv, termProd, PdeRowSpec.bind,
    List.getD_cons_zero, List.getD_cons_succ, map_neg, map_one]
  try push_cast
  try ring

/-- The cross-coupled second-order pair as declared rows: two field
components, two declared jets, width-four exponent tuples — the
multi-component axis of the positional convention exercised. -/
def coupledRowSpec : PdeRowSpec (Fin 2) 2 where
  stateVars := [0, 1]
  jets := [(0, ⟨2, by norm_num⟩), (1, ⟨2, by norm_num⟩)]
  drift i :=
    if i = 0 then [⟨1, [0, 0, 1, 0]⟩, ⟨1, [0, 1, 0, 0]⟩]
    else [⟨1, [0, 0, 0, 1]⟩, ⟨-1, [1, 0, 0, 0]⟩]

/-- The declared coupled-pair rows compile to the coupled mechanism. -/
theorem coupledRowSpec_toMechanism :
    coupledRowSpec.toMechanism = coupledMechanism := by
  simp only [PdeRowSpec.toMechanism, coupledMechanism, PdeMechanism.mk.injEq]
  funext i
  fin_cases i <;>
    · norm_num [coupledRowSpec, toMv, termProd, PdeRowSpec.bind,
        List.getD_cons_zero, List.getD_cons_succ, map_neg, map_one]
      try push_cast
      try ring

/-- **Declared data, wired to the semantic universe**: an ideal point
models the compiled mesh presentation of a declared row specification
exactly when its law is supported on the global periodic solution
records of the compiled mechanism — one line at the frame wiring, for
every declared specification. -/
theorem su_pde_rows_adequacy {ι : Type} [Fintype ι] [Inhabited ι] {k : ℕ}
    (S : PdeRowSpec ι k) (M : RingMesh) {T : Set ℝ} (hT : IsOpen T)
    (μ : SubPMF (HeatRec (ι → ℝ))) :
    idealPoint μ ∈ ((S.toMechanism).rows.meshDnf M T).modelClass ↔
      suppC ((S.toMechanism).rows.classicalRecs M T) μ :=
  su_pde_adequacy S.toMechanism M hT μ

end InstanceTies

/-! ## The noise-spectrum declaration and its derived covariance data -/

/-- Which trig family a Fourier-basis element belongs to (a closed
vocabulary: the basis of a declared domain is not extensible data). -/
inductive TrigKind
  | /-- The odd family. -/ sin
  | /-- The even family. -/ cos
deriving DecidableEq, Repr

/-- One term of a driver's spatial shape: `coeff` times the domain's
**orthonormal** Fourier-basis element `(kind, mode)`.  Shapes are
declared in orthonormal coordinates, so the derived covariance
identities and Parseval hold exactly in `ℚ`. -/
structure FourierTermDecl where
  /-- The trig family. -/
  kind : TrigKind
  /-- The mode number. -/
  mode : ℕ
  /-- The exact-rational coefficient. -/
  coeff : ℚ

/-- One noise driver: a spatial shape (finite combination of basis
elements) and a constant amplitude.  The constant-amplitude stratum is
additive noise; multiplicative columns are a declared fence, not a
schema change. -/
structure DriverDecl where
  /-- The spatial shape. -/
  shape : List FourierTermDecl
  /-- The constant amplitude. -/
  amp : ℚ

/-- The tail form of a noise spectrum: what lies beyond the explicit
drivers, in exactly one of three shapes.  There is deliberately no
fourth "absent" shape and no default — a tail read as zero by silence
would convert a trace-class or cylindrical declaration into a
finite-rank one and understate every derived floor. -/
inductive TailFormDecl
  | /-- Finite rank: no spectral mass beyond the explicit drivers —
    present and saying so. -/
    zero
  | /-- Trace-class: a rational enclosure `[lo, hi]` on the tail
    trace. -/
    bracket (lo hi : ℚ)
  | /-- Cylindrical, declared: infinite trace stated as data.  The
    plain-trace consumer refuses this arm. -/
    divergent
deriving DecidableEq, Repr

/-- A noise-spectrum declaration: driver rows plus the tail form.  The
tail is a **required field** — a spectrum without a declared tail is
unrepresentable at this stratum, mirroring the schema's
constructor-required design. -/
structure SpectrumDecl where
  /-- The explicit driver rows. -/
  drivers : List DriverDecl
  /-- The required tail form. -/
  tail : TailFormDecl

namespace SpectrumDecl

/-- The summed coefficient of a shape at one basis element: duplicate
declarations of an element **sum** (grouping before squaring). -/
def groupedCoeff (kd : TrigKind) (md : ℕ) : List FourierTermDecl → ℚ
  | [] => 0
  | t :: ts =>
    (if t.kind = kd ∧ t.mode = md then t.coeff else 0) + groupedCoeff kd md ts

/-- The distinct basis elements a shape mentions. -/
def elems (s : List FourierTermDecl) : List (TrigKind × ℕ) :=
  (s.map fun t => (t.kind, t.mode)).dedup

/-- The squared norm of a driver's shape on the orthonormal basis:
coefficients grouped per element, then squared and summed; `sin` at
mode 0 names the zero function and is massless. -/
def norm2 (s : List FourierTermDecl) : ℚ :=
  ((elems s).map fun e =>
    if e = (TrigKind.sin, 0) then 0 else groupedCoeff e.1 e.2 s ^ 2).sum

/-- The explicit part of the covariance trace: Parseval on the
orthonormal basis, each driver weighted by its squared amplitude —
derived from the declaration, never stored. -/
def explicitTrace (S : SpectrumDecl) : ℚ :=
  (S.drivers.map fun d => d.amp ^ 2 * norm2 d.shape).sum

/-- The derived diagonal of the covariance at one basis element (the
q-table read): the sum over drivers of the squared amplitude-weighted
grouped coefficient. -/
def qDiag (S : SpectrumDecl) (kd : TrigKind) (md : ℕ) : ℚ :=
  if (kd, md) = (TrigKind.sin, 0) then 0
  else (S.drivers.map fun d => (d.amp * groupedCoeff kd md d.shape) ^ 2).sum

/-- The support of a spectrum: every basis element any driver
mentions. -/
def support (S : SpectrumDecl) : Finset (TrigKind × ℕ) :=
  (S.drivers.map fun d => (elems d.shape).toFinset).foldr (· ∪ ·) ∅

/-- A grouped coefficient vanishes off a shape's element list. -/
theorem groupedCoeff_eq_zero_of_not_mem {kd : TrigKind} {md : ℕ} :
    ∀ {s : List FourierTermDecl}, (kd, md) ∉ elems s →
      groupedCoeff kd md s = 0
  | [], _ => rfl
  | t :: ts, h => by
    have hne : ¬(t.kind = kd ∧ t.mode = md) := by
      rintro ⟨h1, h2⟩
      apply h
      refine List.mem_dedup.mpr (List.mem_map.mpr ⟨t, List.mem_cons_self .., ?_⟩)
      simp [h1, h2]
    have hts : (kd, md) ∉ elems ts := by
      intro hc
      apply h
      obtain ⟨u, hu, he⟩ := List.mem_map.mp (List.mem_dedup.mp hc)
      exact List.mem_dedup.mpr
        (List.mem_map.mpr ⟨u, List.mem_cons_of_mem _ hu, he⟩)
    simp [groupedCoeff, hne,
      groupedCoeff_eq_zero_of_not_mem (s := ts) hts]

/-- A driver's squared norm as a sum over any superset of its
elements: the extension is free because grouped coefficients vanish
off the element list. -/
theorem norm2_eq_sum_superset (s : List FourierTermDecl)
    {F : Finset (TrigKind × ℕ)} (hF : (elems s).toFinset ⊆ F) :
    norm2 s = ∑ e ∈ F,
      (if e = (TrigKind.sin, 0) then 0 else groupedCoeff e.1 e.2 s ^ 2) := by
  have hnd : (elems s).Nodup := List.nodup_dedup _
  rw [norm2, ← List.sum_toFinset _ hnd]
  refine Finset.sum_subset hF fun e _ he => ?_
  have he' : e ∉ elems s := fun hc => he (List.mem_toFinset.mpr hc)
  rcases e with ⟨kd, md⟩
  norm_num [groupedCoeff_eq_zero_of_not_mem he']

/-- Every driver's element list lands inside the fold of a driver
list containing it. -/
theorem elems_subset_foldr {d : DriverDecl} :
    ∀ ds : List DriverDecl, d ∈ ds →
      (elems d.shape).toFinset ⊆
        (ds.map fun u => (elems u.shape).toFinset).foldr (· ∪ ·) ∅
  | [], hd => nomatch hd
  | a :: ts, hd => by
    rcases List.mem_cons.mp hd with rfl | hmem
    · intro e he
      simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
      exact .inl he
    · intro e he
      simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
      exact .inr (elems_subset_foldr ts hmem he)

/-- Every driver's element list lands inside the spectrum's support. -/
theorem elems_subset_support (S : SpectrumDecl) {d : DriverDecl}
    (hd : d ∈ S.drivers) : (elems d.shape).toFinset ⊆ S.support :=
  elems_subset_foldr S.drivers hd

/-- **The trace is the sum of the derived diagonal over the support**:
the explicit trace equals the summed q-table — off-diagonal entries of
the derived covariance never enter a trace.  (Finite Fubini over the
declaration.) -/
theorem explicitTrace_eq_sum_qDiag (S : SpectrumDecl) :
    S.explicitTrace = ∑ e ∈ S.support, S.qDiag e.1 e.2 := by
  rcases S with ⟨drivers, tail⟩
  induction drivers with
  | nil => simp [explicitTrace, qDiag, support]
  | cons d ts ih =>
    have hsub : (elems d.shape).toFinset ⊆
        (SpectrumDecl.mk (d :: ts) tail).support :=
      elems_subset_support _ (List.mem_cons_self ..)
    have hsub' : (SpectrumDecl.mk ts tail).support ⊆
        (SpectrumDecl.mk (d :: ts) tail).support := by
      intro e he
      simp only [support, List.map_cons, List.foldr_cons, Finset.mem_union]
      exact .inr he
    -- the head driver's contribution, over the big support
    have hhead : d.amp ^ 2 * norm2 d.shape =
        ∑ e ∈ (SpectrumDecl.mk (d :: ts) tail).support,
          (if e = (TrigKind.sin, 0) then 0
           else (d.amp * groupedCoeff e.1 e.2 d.shape) ^ 2) := by
      rw [norm2_eq_sum_superset d.shape hsub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e = (TrigKind.sin, 0)
      · simp [he]
      · simp only [he, if_false]
        ring
    -- the tail drivers' contribution, extended to the big support
    have htail : (SpectrumDecl.mk ts tail).explicitTrace =
        ∑ e ∈ (SpectrumDecl.mk (d :: ts) tail).support,
          (SpectrumDecl.mk ts tail).qDiag e.1 e.2 := by
      rw [ih]
      refine Finset.sum_subset hsub' fun e _ he => ?_
      rcases e with ⟨kd, md⟩
      by_cases hsin : ((kd, md) : TrigKind × ℕ) = (TrigKind.sin, 0)
      · simp [qDiag, hsin]
      · have hzero : ∀ u ∈ ts, (u.amp * groupedCoeff kd md u.shape) ^ 2
            = (0 : ℚ) := by
          intro u hu
          have hnm : (kd, md) ∉ elems u.shape := by
            intro hc
            exact he (elems_subset_support (SpectrumDecl.mk ts tail) hu
              (List.mem_toFinset.mpr hc))
          simp [groupedCoeff_eq_zero_of_not_mem hnm]
        simp only [qDiag, hsin, if_false]
        exact List.sum_eq_zero fun x hx => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
          exact hzero u hu
    calc (SpectrumDecl.mk (d :: ts) tail).explicitTrace
        = d.amp ^ 2 * norm2 d.shape
            + (SpectrumDecl.mk ts tail).explicitTrace := by
          simp [explicitTrace]
      _ = ∑ e ∈ (SpectrumDecl.mk (d :: ts) tail).support,
            ((if e = (TrigKind.sin, 0) then 0
              else (d.amp * groupedCoeff e.1 e.2 d.shape) ^ 2)
              + (SpectrumDecl.mk ts tail).qDiag e.1 e.2) := by
          rw [hhead, htail, Finset.sum_add_distrib]
      _ = ∑ e ∈ (SpectrumDecl.mk (d :: ts) tail).support,
            (SpectrumDecl.mk (d :: ts) tail).qDiag e.1 e.2 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rcases e with ⟨kd, md⟩
          by_cases hsin : ((kd, md) : TrigKind × ℕ) = (TrigKind.sin, 0) <;>
            simp [qDiag, hsin]

/-- The plain trace of a declared spectrum, as an exact enclosure —
**total-or-refusing**: the `zero` tail returns the explicit trace
exactly; the `bracket` tail widens by its enclosure; the `divergent`
tail has **no plain trace** and the read refuses (`none`) — never a
default, never zero. -/
def plainTrace (S : SpectrumDecl) : Option (ℚ × ℚ) :=
  match S.tail with
  | .zero => some (S.explicitTrace, S.explicitTrace)
  | .bracket lo hi => some (S.explicitTrace + lo, S.explicitTrace + hi)
  | .divergent => none

/-- **The refusal is structural**: a declared-divergent tail admits no
plain-trace read, whatever the drivers. -/
theorem plainTrace_divergent_none (ds : List DriverDecl) :
    (SpectrumDecl.mk ds .divergent).plainTrace = none := rfl

end SpectrumDecl

/-! ### The certified stochastic-heat spectrum, recomputed by theorem

Five drivers on the `sin` basis realize the certified q-table
`q₁ = 1/5`, `q₂ = 3/50` as sums of rational squares
(`1/5 = (1/5)² + (2/5)²`; `3/50 = (1/10)² + (1/10)² + (1/5)²` — the
per-mode standard deviations are irrational, the squared driver
columns are not), with unit amplitudes and a zero tail. -/

section HeatSpectrum

open SpectrumDecl

/-- The declared spectrum of the certified stochastic-heat instance. -/
def heatSpectrum : SpectrumDecl where
  drivers :=
    [⟨[⟨.sin, 1, 1/5⟩], 1⟩,
     ⟨[⟨.sin, 1, 2/5⟩], 1⟩,
     ⟨[⟨.sin, 2, 1/10⟩], 1⟩,
     ⟨[⟨.sin, 2, 1/10⟩], 1⟩,
     ⟨[⟨.sin, 2, 1/5⟩], 1⟩]
  tail := .zero

/-- The derived explicit trace of the certified spectrum: `13/50`,
exactly. -/
theorem heatSpectrum_trace : heatSpectrum.explicitTrace = 13/50 := by
  norm_num [heatSpectrum, explicitTrace, norm2, elems, groupedCoeff,
    List.dedup]

/-- The derived q-table at mode 1: `1/5`, exactly. -/
theorem heatSpectrum_qDiag_one : heatSpectrum.qDiag .sin 1 = 1/5 := by
  norm_num [heatSpectrum, qDiag, groupedCoeff]

/-- The derived q-table at mode 2: `3/50`, exactly. -/
theorem heatSpectrum_qDiag_two : heatSpectrum.qDiag .sin 2 = 3/50 := by
  norm_num [heatSpectrum, qDiag, groupedCoeff]

/-- The derived diagonal vanishes off the declared support. -/
theorem heatSpectrum_qDiag_off : heatSpectrum.qDiag .cos 1 = 0 := by
  norm_num [heatSpectrum, qDiag, groupedCoeff,
    show TrigKind.sin ≠ TrigKind.cos from fun h => nomatch h]

/-- The plain trace of the certified spectrum: the zero tail returns
the explicit trace as a width-zero enclosure. -/
theorem heatSpectrum_plainTrace :
    heatSpectrum.plainTrace = some (13/50, 13/50) := by
  rw [show heatSpectrum.plainTrace
      = some (heatSpectrum.explicitTrace, heatSpectrum.explicitTrace) from rfl,
    heatSpectrum_trace]

/-- The certified floor identity, exact: the derived trace over twice
the viscosity — `(13/50) / (2·(1/10)) = 13/10`. -/
theorem heat_floor_exact : (13/50 : ℚ) / (2 * (1/10)) = 13/10 := by
  norm_num

/-- A bracket tail widens the plain trace by its enclosure (the heat
drivers under a `[0, 1/50]` tail bracket). -/
theorem bracket_plainTrace :
    (SpectrumDecl.mk heatSpectrum.drivers (.bracket 0 (1/50))).plainTrace
      = some (13/50, 7/25) := by
  have ht : (SpectrumDecl.mk heatSpectrum.drivers
      (.bracket 0 (1/50))).explicitTrace = 13/50 := heatSpectrum_trace
  rw [show (SpectrumDecl.mk heatSpectrum.drivers (.bracket 0 (1/50))).plainTrace
      = some ((SpectrumDecl.mk heatSpectrum.drivers (.bracket 0 (1/50))).explicitTrace + 0,
          (SpectrumDecl.mk heatSpectrum.drivers (.bracket 0 (1/50))).explicitTrace + 1/50)
      from rfl, ht]
  norm_num

/-! ### Controls: each exists because a mutant needs a witness -/

/-- **Grouping control**: duplicate declarations of one basis element
sum before squaring — `(1/10 + 1/10)² = 1/25`, never
`(1/10)² + (1/10)² = 1/50`. -/
theorem dupSpec_grouping :
    SpectrumDecl.norm2 [⟨.sin, 1, 1/10⟩, ⟨.sin, 1, 1/10⟩] = 1/25 := by
  norm_num [norm2, elems, groupedCoeff, List.dedup]

/-- **Masslessness control**: `sin` at mode 0 names the zero function
and contributes no mass, whatever its declared coefficient. -/
theorem sin0_massless :
    SpectrumDecl.norm2 [⟨.sin, 0, 5⟩] = 0 := by
  norm_num [norm2, elems, groupedCoeff, List.dedup]

end HeatSpectrum

end Adequacy
end SuFunctor

#print axioms SuFunctor.Adequacy.termProd_congr
#print axioms SuFunctor.Adequacy.toMv_congr
#print axioms SuFunctor.Adequacy.PdeRowSpec.toMechanism_congr_inhabited
#print axioms SuFunctor.Adequacy.heatRowSpec_toMechanism
#print axioms SuFunctor.Adequacy.heatAt_iff_rowsAt
#print axioms SuFunctor.Adequacy.heat_rows_adequacy
#print axioms SuFunctor.Adequacy.burgersRowSpec_toMechanism
#print axioms SuFunctor.Adequacy.kppRowSpec_toMechanism
#print axioms SuFunctor.Adequacy.coupledRowSpec_toMechanism
#print axioms SuFunctor.Adequacy.su_pde_rows_adequacy
#print axioms SuFunctor.Adequacy.SpectrumDecl.groupedCoeff_eq_zero_of_not_mem
#print axioms SuFunctor.Adequacy.SpectrumDecl.norm2_eq_sum_superset
#print axioms SuFunctor.Adequacy.SpectrumDecl.explicitTrace_eq_sum_qDiag
#print axioms SuFunctor.Adequacy.SpectrumDecl.plainTrace_divergent_none
#print axioms SuFunctor.Adequacy.heatSpectrum_trace
#print axioms SuFunctor.Adequacy.heatSpectrum_qDiag_one
#print axioms SuFunctor.Adequacy.heatSpectrum_qDiag_two
#print axioms SuFunctor.Adequacy.heatSpectrum_qDiag_off
#print axioms SuFunctor.Adequacy.heatSpectrum_plainTrace
#print axioms SuFunctor.Adequacy.heat_floor_exact
#print axioms SuFunctor.Adequacy.bracket_plainTrace
#print axioms SuFunctor.Adequacy.dupSpec_grouping
#print axioms SuFunctor.Adequacy.sin0_massless
