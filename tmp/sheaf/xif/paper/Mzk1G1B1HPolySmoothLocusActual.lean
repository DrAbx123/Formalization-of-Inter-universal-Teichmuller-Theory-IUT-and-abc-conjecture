/-
# B1 / O3(ii)(b) — the `t`-chart smooth ↔ derivative bridge `hbridge`, at the scheme level

Consumer: `Mzk1G1B1HPolyBranchSchemeActual.hPoly_ram_subset_derivative` (which takes
`hbridge` as an explicit parameter), hence `Mzk1G1B1HbObligationsActual` and the B1 branch
lane (`Mzk1G1PhiFixedLBranchSupportActual`).  The same `dt`/`du` dictionary is re-used by the
B3 ramification-divisor lane.

## Goal

`hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h`, i.e.
`q ∈ Ram (chartMorphismInf h) → h'(λ) ∈ q` for a prime `q` of the source ring `ℚ[t]` of the
`t`-chart morphism `chartMorphismInf h = Spec.map (evalAt h) ≫ localChartInf`.

## What is proved here (no sorry, no admit, no new axiom)

1. `chartMorphismInf_locallyOfFinitePresentation` / `specMap_evalAt_locallyOfFinitePresentation`:
   both morphisms are locally of finite presentation **unconditionally** (the ring-theoretic input
   `RingHom.FinitePresentation (evalAt a)` is `Mzk1G1B1HPolyLoFPActual.evalAt_finitePresentation`).
2. `smoothLocus_chartInf_eq_specMap` and its pointwise forms (`mem_chartInf_smoothLocus_iff`,
   `chartInf_smoothLocus_iff_specMap`): **the smooth locus of the `t`-chart morphism is the
   smooth locus of `Spec.map (evalAt h)`** — the open immersion `localChartInf` does not change it
   (donor `BelyiRamification.smoothLocus_comp_of_isOpenImmersion`).  This is the scheme-level
   reduction of the whole task to the single ring map `evalAt h : ℚ[λ] →+* ℚ[t]`.
3. `SmoothCriterion`: the smooth ↔ derivative criterion, as a named `Prop` — this is the
   **remaining obligation**, see below.
4. `smoothAt_chartInf_iff` (task declaration 1), `ram_chartInf_iff_derivative_mem` (`Ram` form),
   `smoothCriterion_iff_ram`, and `ram_eq_derivativeZeroSet_of_hcrit`: the criterion in both
   shapes, and the fact that it upgrades `hbridge` to the set equality
   `Ram (chartMorphismInf h) = derivativeZeroSet h`.
5. `hbridge_of_smooth_criterion` / `hbridge_of_hcrit` (task declaration 2), and the degenerate case
   `hbridge_of_derivative_eq_zero` (`h' = 0` implies `derivativeZeroSet h = univ`).
6. `hpts_of_hbridge` (task declaration 3, donor shape), the correctly shaped in-chart piece
   `branch_image_ram_inter_chart0_subset`, and the reduction of the full bridge `hpts` to it plus
   an explicit out-of-chart obligation (`hpts_of_hbridge_and_out`,
   `hpts_union_p1Zero_of_hbridge_and_out`).
7. `hbH_of_value_and_ram_union_p1Zero` / `hbH_of_hbridge_and_out`: the repaired O3(ii)(b)
   reduction (see the interface defect below).

## Remaining obligation (`hcrit`): `SmoothCriterion h`

  `SmoothCriterion h  :=  ∀ q : Spec ℚ[t], q ∈ (chartMorphismInf (R := ℚ[λ]) h).smoothLocus ↔ h' ∉ q`,

equivalently (`smoothCriterion_iff_ram`) `q ∈ Ram (chartMorphismInf h) ↔ h' ∈ q`.

By (2) this is the statement that `Spec.map (evalAt h)` — the map `λ ↦ h(λ)` of affine lines — is
smooth at `q` exactly where the derivative does not vanish, i.e.
`Algebra.FormallySmooth ℚ[λ] (ℚ[t]_q) ↔ h' ∉ q` (`Algebra.IsSmoothAt`).  The tree contains **no**
scheme-level "smooth at `q` ⟺ derivative non-zero at `q`" bridge (grep for
`smooth_of_`/`Kaehler`/`Jacobian`/`derivative` in `AlgebraicGeometry` finds nothing of this shape),
so it is kept as an explicit hypothesis `hcrit` in every declaration that needs it.
Proof plan, with the pieces that *do* exist in Mathlib:

* (⟸) `h' ∉ q` implies smooth at `q`.  Let `R = ℚ[λ]`, `A = ℚ[t]`, `S := A_{h'} = A[1/h']`.
  Then `S ≅ R[T, 1/h'(T)] / (λ - h(T))` (send `T ↦ t`): a **one-generator, one-relation
  submersive presentation** whose Jacobian is `∂(λ - h(T))/∂T = -h'(T)`, invertible in `S` by
  construction.  So `Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension 0`, then
  `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth` and the instance
  `Algebra.IsStandardSmooth → Algebra.Smooth`
  (`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`) give `Algebra.Smooth R S`, hence
  `Algebra.FormallySmooth R S`.  Finally `Algebra.basicOpen_subset_smoothLocus_iff`
  (`Mathlib/RingTheory/Smooth/Locus.lean`) turns `FormallySmooth R A_{h'}` into `D(h') ⊆ smoothLocus`.
  What a full formalisation still needs is the `AlgEquiv`
  `A_{h'} ≃ₐ[R] (MvPolynomial (Fin 1) R ⧸ Ideal.span {C λ - h(T)})_{h'}` (a `IsLocalization.Away`
  comparison; `SubmersivePresentation` API bookkeeping only).
* (⟹) smooth at `q` implies `h' ∉ q`.  `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth` gives
  `f ∉ q` with `Algebra.IsStandardSmooth R (A_f)`, and
  `Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential` makes `Ω[A_f⁄R]` free.  But
  `Ω[ℚ[t]⁄ℚ[λ]] ≅ ℚ[t]/(h')` (Kähler differentials of the presentation: `d(λ - h(T)) = -h'(T)dT`,
  so `Ω ≅ A dT/(h'dT) ≅ A/(h')`), hence `Ω[A_f⁄R] ≅ A_f/(h')` (`Ω[A_f⁄R] ≅ A_f ⊗_A Ω[A⁄R]`).
  For `0 ≠ h' ∈ q` this is a **non-zero module with torsion** over the domain `A_f`
  (`h' • 1 = 0`), so it is not free: contradiction.  The missing formal ingredients are the Kähler
  computation `Ω[A⁄R] ≅ A/(h')` (through `KaehlerDifferential.kerCotangentToTensor` for the
  principal ideal `(λ - h(T))`) and its localization compatibility.

The degenerate case `h' = 0` is closed here without the criterion (`hbridge_of_derivative_eq_zero`),
because then `derivativeZeroSet h = univ`.

## Interface defect in the donor `hpts` (read before using it)

The donor obligation

  `hpts : Branch (hPoly h hh) ⊆ chartMorphismInf (R := ℚ[λ]) h '' derivativeZeroSet h`

is **geometrically false as stated** once `2 ≤ deg h`.  Indeed
`chartMorphismInf h = Spec.map (evalAt h) ≫ localChartInf`, so its image is contained in the
`t`-chart `Set.range localChartInf`, which is `ℙ¹ ∖ {λ = 0} = ℙ¹ ∖ p1Zero`; thus `hpts` forces
`Branch (hPoly) ⊆ Set.range localChartInf` (`branch_subset_range_of_hpts`, proved below).  But the
value `0` is a critical value of a Belyi polynomial (so `p1Zero ∈ Branch`), and for `2 ≤ deg h` the
point `t = ∞` is a ramification point with value `h(∞) = ∞`, whose image point in the `λ`-chart is
again `λ = 0`, i.e. `p1Zero`.  So `hpts` cannot be discharged for the B1 polynomial, and the
reduction `hbH_of_value_and_ram` cannot be completed with it.

The geometrically correct statement adds the single point `p1Zero`, which is harmless for `hbH`
because `p1Zero ⊆ boundarySetGlued`:

  `hpts' : Branch (hPoly h hh) ⊆ chartMorphismInf (R := ℚ[λ]) h '' derivativeZeroSet h ∪ p1Zero`,

and `hbH` follows from `hpts'` and the value layer (`hbH_of_value_and_ram_union_p1Zero`, proved
here).  `hpts'` splits along the `t`-chart:

* the **in-chart** piece `(hPoly) '' (Ram (hPoly) ∩ range localChartInf)` is closed here from
  `hbridge` alone (`branch_image_ram_inter_chart0_subset`): a ramified point of `hPoly` inside the
  `t`-chart is `localChartInf x` with `x ∈ Ram (chartMorphismInf h)` (donor
  `ram_hPoly_inter_chart0_eq`), and its value is `chartMorphismInf x` (donor `hPoly_chart0_apply`),
  so `x` itself is the required derivative-zero prime;
* the **out-of-chart** piece is the explicit obligation `hout` of
  `hpts_union_p1Zero_of_hbridge_and_out`.  Proof plan: a point of `ℙ¹` outside
  `range localChartInf` is `p1Zero = localChart0 (chartPrime 0)` (`λ = 0`, `t = ∞`); on the
  `λ`-chart `hPoly` is `chartMorphism0 (hPolyLam h)` with `hPolyLam h = t^d / hRev(t)`
  (`hPoly_ι_c2`), and `hRev 0 = leadingCoeff h ≠ 0` for `0 < h.natDegree`, so
  `hPoly p1Zero = p1Zero`.  (The `t`-coordinates here are the `λ`-chart coordinates of the two
  copies of `ℙ¹`, i.e. `λ = 1/t`.)

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1B1HPolyBranchSchemeActual
import tmp.sheaf.xif.paper.Mzk1G1B1HPolyLoFPActual
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolySmoothLocusActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLoFPActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PhiFixedLChartInfBoundaryActual

/-! ## 1. Both morphisms are locally of finite presentation (unconditional) -/

/-- `Spec.map (evalAt a)`, the substitution `λ ↦ a`, is locally of finite presentation for every
`a ∈ ℚ[t]`.  Ring-theoretic input: `Mzk1G1B1HPolyLoFPActual.evalAt_finitePresentation`. -/
theorem specMap_evalAt_locallyOfFinitePresentation (a : Polynomial ℚ) :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt a))) :=
  locallyOfFinitePresentation_specMap a (evalAt_finitePresentation a)

/-- The `t`-chart morphism `chartMorphismInf a = Spec.map (evalAt a) ≫ localChartInf` is locally of
finite presentation for every `a ∈ ℚ[t]` (the second factor is an open immersion).
Ring-theoretic input: `Mzk1G1B1HPolyLoFPActual.evalAt_finitePresentation`. -/
theorem chartMorphismInf_locallyOfFinitePresentation (a : Polynomial ℚ) :
    LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) a) :=
  locallyOfFinitePresentation_chartMorphismInf a (evalAt_finitePresentation a)

/-! ## 2. The smooth locus of the chart morphism is that of `Spec.map (evalAt h)` -/

/-- **The open immersion `localChartInf` does not change the smooth locus.**  Since
`chartMorphismInf a = Spec.map (evalAt a) ≫ localChartInf` and `localChartInf` is an open
immersion, `smoothLocus (chartMorphismInf a) = smoothLocus (Spec.map (evalAt a))` (donor
`BelyiRamification.smoothLocus_comp_of_isOpenImmersion`).  This is the scheme-level reduction of
`hbridge` to the ring map `evalAt h`. -/
theorem smoothLocus_chartInf_eq_specMap {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt a)))]
    [LocallyOfFinitePresentation (chartMorphismInf (R := R) a)] :
    (chartMorphismInf (R := R) a).smoothLocus =
      (Spec.map (CommRingCat.ofHom (evalAt a))).smoothLocus := by
  have h := smoothLocus_comp_of_isOpenImmersion
    (f := Spec.map (CommRingCat.ofHom (evalAt a))) (g := localChartInf)
  exact h

/-- Pointwise form of `smoothLocus_chartInf_eq_specMap`: smoothness of the `t`-chart morphism at
`p` is smoothness of `Spec.map (evalAt a)` at `p`. -/
theorem mem_chartInf_smoothLocus_iff {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt a)))]
    [LocallyOfFinitePresentation (chartMorphismInf (R := R) a)]
    (p : PrimeSpectrum R) :
    p ∈ (chartMorphismInf (R := R) a).smoothLocus ↔
      p ∈ (Spec.map (CommRingCat.ofHom (evalAt a))).smoothLocus := by
  rw [smoothLocus_chartInf_eq_specMap a]

/-- The same reduction in stalk-map (`FormallySmooth`) form: at `p`, the `t`-chart morphism is
formally smooth iff the stalk map of `Spec.map (evalAt a)` is. -/
theorem chartInf_smoothLocus_iff_specMap {R : Type} [CommRing R] [Algebra ℚ R] (a : R)
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (evalAt a)))]
    [LocallyOfFinitePresentation (chartMorphismInf (R := R) a)]
    (p : PrimeSpectrum R) :
    ((chartMorphismInf (R := R) a).stalkMap p).hom.FormallySmooth ↔
      ((Spec.map (CommRingCat.ofHom (evalAt a))).stalkMap p).hom.FormallySmooth := by
  rw [← Scheme.Hom.mem_smoothLocus (f := chartMorphismInf (R := R) a) (x := p),
    ← Scheme.Hom.mem_smoothLocus (f := Spec.map (CommRingCat.ofHom (evalAt a))) (x := p)]
  exact mem_chartInf_smoothLocus_iff a p

/-! ## 3. The smooth ↔ derivative criterion (the remaining obligation) -/

/-- **THE SMOOTH ↔ DERIVATIVE CRITERION** for the `t`-chart of `hPoly` (explicit obligation, not
proved here — see the file header for the proof plan):

  `q ∈ smoothLocus (chartMorphismInf h) ↔ h'(λ) ∉ q`

for every prime `q` of the source ring `ℚ[t]`.

Equivalently (`smoothCriterion_iff_ram`): `q ∈ Ram (chartMorphismInf h) ↔ h'(λ) ∈ q`, i.e.
`Ram (chartMorphismInf h) = derivativeZeroSet h`.

This is the only missing input of the whole `hbridge` lane: everything else is proved in this file. -/
def SmoothCriterion (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)] : Prop :=
  ∀ q : PrimeSpectrum (Polynomial ℚ),
    q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
      Polynomial.derivative h ∉ q.asIdeal

/-- The `smoothLocus` form and the `Ram` form of the criterion are equivalent
(`Ram f = (f.smoothLocus)ᶜ`). -/
theorem smoothCriterion_iff_ram (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)] :
    SmoothCriterion h ↔
      ∀ q : PrimeSpectrum (Polynomial ℚ),
        q ∈ Ram (chartMorphismInf (R := Polynomial ℚ) h) ↔
          Polynomial.derivative h ∈ q.asIdeal := by
  constructor
  · intro hc q
    show ¬ q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
      Polynomial.derivative h ∈ q.asIdeal
    have hq : q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
        Polynomial.derivative h ∉ q.asIdeal := hc q
    tauto
  · intro hc q
    show q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
      Polynomial.derivative h ∉ q.asIdeal
    have hq : ¬ q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
        Polynomial.derivative h ∈ q.asIdeal := hc q
    tauto

/-- **Task declaration 1** (`smoothLocus` form): the criterion gives the pointwise characterization
`q ∈ smoothLocus (chartMorphismInf h) ↔ h' ∉ q`. -/
theorem smoothAt_chartInf_iff (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hcrit : SmoothCriterion h) (q : PrimeSpectrum (Polynomial ℚ)) :
    q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
      Polynomial.derivative h ∉ q.asIdeal :=
  hcrit q

/-- **Task declaration 1** (`Ram` form): the criterion gives `q ∈ Ram (chartMorphismInf h) ↔ h' ∈ q`. -/
theorem ram_chartInf_iff_derivative_mem (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hcrit : SmoothCriterion h) (q : PrimeSpectrum (Polynomial ℚ)) :
    q ∈ Ram (chartMorphismInf (R := Polynomial ℚ) h) ↔
      Polynomial.derivative h ∈ q.asIdeal :=
  (smoothCriterion_iff_ram h).mp hcrit q

/-- **The criterion upgrades `hbridge` to a set equality**: under `SmoothCriterion h`, the
ramification locus of the `t`-chart morphism *is* the derivative-zero set. -/
theorem ram_eq_derivativeZeroSet_of_hcrit (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hcrit : SmoothCriterion h) :
    Ram (chartMorphismInf (R := Polynomial ℚ) h) = derivativeZeroSet h := by
  refine Set.Subset.antisymm ?_ ?_
  · intro q hq
    exact mem_derivativeZeroSet_iff.mpr (by
      by_contra hcon
      exact hq ((hcrit q).mpr hcon))
  · intro q hq
    exact fun hS => ((hcrit q).mp hS) (mem_derivativeZeroSet_iff.mp hq)

/-! ## 4. `hbridge` from the criterion -/

/-- **Task declaration 2, explicit-`∀`-form**: the smooth ↔ derivative criterion implies `hbridge`,
`Ram (chartMorphismInf h) ⊆ derivativeZeroSet h`. -/
theorem hbridge_of_smooth_criterion (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hcrit : ∀ q : PrimeSpectrum (Polynomial ℚ),
      q ∈ (chartMorphismInf (R := Polynomial ℚ) h).smoothLocus ↔
        Polynomial.derivative h ∉ q.asIdeal) :
    Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h := by
  intro q hq
  refine mem_derivativeZeroSet_iff.mpr ?_
  by_contra hcon
  exact hq ((hcrit q).mpr hcon)

/-- **Task declaration 2**: `hbridge` from the named criterion `SmoothCriterion h`.

This is the `hbridge` parameter of the donor
`Mzk1G1B1HPolyBranchSchemeActual.hPoly_ram_subset_derivative` (and hence of
`hbH_of_value_and_ram`). -/
theorem hbridge_of_hcrit (h : Polynomial ℚ)
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hcrit : SmoothCriterion h) :
    Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h :=
  hbridge_of_smooth_criterion h hcrit

/-- Degenerate case `h' = 0`: the derivative-zero set is everything. -/
theorem derivativeZeroSet_eq_univ_of_derivative_eq_zero {h : Polynomial ℚ}
    (h0 : Polynomial.derivative h = 0) : derivativeZeroSet h = Set.univ := by
  ext q
  rw [derivativeZeroSet, Set.mem_setOf_eq, h0]
  simp

/-- **`hbridge` in the degenerate case `h' = 0`** (no criterion needed). -/
theorem hbridge_of_derivative_eq_zero {h : Polynomial ℚ}
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (h0 : Polynomial.derivative h = 0) :
    Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h := by
  rw [derivativeZeroSet_eq_univ_of_derivative_eq_zero h0]
  exact Set.subset_univ _

/-! ## 5. `hpts`: from `hbridge` to the branch locus -/

/-- The image of `chartMorphismInf a` lies in the `t`-chart (`chartMorphismInf a` is the `t`-chart
morphism, hence its image is contained in `Set.range localChartInf`). -/
theorem chartInf_mem_range (a : Polynomial ℚ) (p : PrimeSpectrum (Polynomial ℚ)) :
    (chartMorphismInf (R := Polynomial ℚ) a).base p ∈ Set.range localChartInf.base :=
  ⟨PrimeSpectrum.comap (evalAt a) p, (chartMorphismInf_apply a p).symm⟩

/-- **Consequence of the donor `hpts`**: it forces the whole branch locus into the `t`-chart.  See
the file header: this is why `hpts` is false as stated for `2 ≤ deg h`. -/
theorem branch_subset_range_of_hpts (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hpts : Branch (hPoly h hh) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h) :
    Branch (hPoly h hh) ⊆ Set.range localChartInf.base := by
  refine hpts.trans ?_
  intro y hy
  obtain ⟨q, -, rfl⟩ := hy
  exact chartInf_mem_range h q

/-- **Task declaration 3 (donor shape)**: `hbridge` implies that the part of `Ram (hPoly)` lying in
the `t`-chart maps into `localChartInf '' derivativeZeroSet` (donor `hPoly_ram_subset_derivative`,
i.e. `ram_hPoly_inter_chart0_eq` plus monotonicity). -/
theorem hpts_of_hbridge (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h) :
    Ram (hPoly h hh) ∩ Set.range localChartInf.base ⊆
      localChartInf.base '' derivativeZeroSet h :=
  hPoly_ram_subset_derivative h hh hbridge

/-- **The correctly shaped `t`-chart piece of the branch locus** (the shape the consumer
`hbH_of_value_and_ram` needs, unlike the `localChartInf '' …` shape of `hpts_of_hbridge`): a
ramification point `z` of `hPoly` that lies in the `t`-chart is `localChartInf x` with
`x ∈ Ram (chartMorphismInf h)` (donor `ram_hPoly_inter_chart0_eq`), and its value is
`chartMorphismInf x` (donor `hPoly_chart0_apply`); so `x` itself is the required derivative-zero
prime.  Hence `hbridge` alone covers the in-chart piece of `hpts`. -/
theorem branch_image_ram_inter_chart0_subset (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h) :
    (hPoly h hh) '' (Ram (hPoly h hh) ∩ Set.range localChartInf.base) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h := by
  rintro y ⟨z, ⟨hzRam, hzrange⟩, rfl⟩
  obtain ⟨x, rfl⟩ := hzrange
  have hx : x ∈ Ram (chartMorphismInf (R := Polynomial ℚ) h) := by
    have hmem : localChartInf.base x ∈ Ram (hPoly h hh) ∩ Set.range localChartInf.base :=
      ⟨hzRam, ⟨x, rfl⟩⟩
    rw [ram_hPoly_inter_chart0_eq h hh] at hmem
    obtain ⟨x', hx', hxx'⟩ := hmem
    have hxx : x' = x := localChartInf.isOpenEmbedding.injective hxx'
    exact hxx ▸ hx'
  refine ⟨x, hbridge hx, ?_⟩
  rw [hPoly_chart0_apply h hh x, chartMorphismInf_apply]

/-- **`hpts` from `hbridge` and the out-of-chart piece** (task declaration 4, in-chart half
proved): if the part of the branch locus coming from ramification points outside the `t`-chart
already lies in the `chartMorphismInf`-image of the derivative-zero set, then so does the whole
branch locus. -/
theorem hpts_of_hbridge_and_out (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h)
    (hout : (hPoly h hh) '' (Ram (hPoly h hh) \ Set.range localChartInf.base) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h) :
    Branch (hPoly h hh) ⊆ chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  by_cases hzr : z ∈ Set.range localChartInf.base
  · exact branch_image_ram_inter_chart0_subset h hh hbridge ⟨z, ⟨hz, hzr⟩, rfl⟩
  · exact hout ⟨z, ⟨hz, hzr⟩, rfl⟩

/-! ## 6. The repaired O3(ii)(b) reduction (`hpts` plus the point `p1Zero`) -/

/-- **`hpts` with `p1Zero` added** (the geometrically correct statement, see the file header),
from `hbridge` and the out-of-chart piece. -/
theorem hpts_union_p1Zero_of_hbridge_and_out (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h)
    (hout : (hPoly h hh) '' (Ram (hPoly h hh) \ Set.range localChartInf.base) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h ∪ p1Zero) :
    Branch (hPoly h hh) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h ∪ p1Zero := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  by_cases hzr : z ∈ Set.range localChartInf.base
  · exact Or.inl (branch_image_ram_inter_chart0_subset h hh hbridge ⟨z, ⟨hz, hzr⟩, rfl⟩)
  · exact hout ⟨z, ⟨hz, hzr⟩, rfl⟩

/-- **Task declaration 3 repaired — the O3(ii)(b) reduction with the correct target**: `hbH`
(`Branch (hPoly h hh) ⊆ boundarySetGlued`) follows from the value layer (grace's O3, DONE) and the
corrected bridge `hpts'` (branch locus in the derivative-zero image *plus* the point `p1Zero`).
This is the honest replacement for
`Mzk1G1B1HPolyBranchSchemeActual.hbH_of_value_and_ram`, whose hypothesis `hpts` is unprovable for
`2 ≤ deg h` (see the file header): the extra point `p1Zero` is harmless because
`p1Zero ⊆ boundarySetGlued`. -/
theorem hbH_of_value_and_ram_union_p1Zero (h : Polynomial ℚ) (hh : h ≠ 0)
    (hdeg : 0 < h.natDegree)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hval : ValueLayer h)
    (hpts : Branch (hPoly h hh) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h ∪ p1Zero) :
    Branch (hPoly h hh) ⊆ boundarySetGlued := by
  intro y hy
  rcases hpts hy with ⟨q, hq, rfl⟩ | hz
  · have hq' : Polynomial.derivative h ∈ q.asIdeal := mem_derivativeZeroSet_iff.mp hq
    rw [chartMorphismInf_mem_boundarySetGlued_iff]
    exact critical_prime_value_mem_or_sub_one hdeg hval hq'
  · exact Or.inl (Or.inl hz)

/-- **The repaired reduction, wired to `hbridge`**: the hypotheses are `hbridge` (the smooth ↔
derivative bridge, task declaration 2), the out-of-chart piece `hout`, and the value layer. -/
theorem hbH_of_hbridge_and_out (h : Polynomial ℚ) (hh : h ≠ 0) (hdeg : 0 < h.natDegree)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h)]
    (hval : ValueLayer h)
    (hbridge : Ram (chartMorphismInf (R := Polynomial ℚ) h) ⊆ derivativeZeroSet h)
    (hout : (hPoly h hh) '' (Ram (hPoly h hh) \ Set.range localChartInf.base) ⊆
      chartMorphismInf (R := Polynomial ℚ) h '' derivativeZeroSet h ∪ p1Zero) :
    Branch (hPoly h hh) ⊆ boundarySetGlued :=
  hbH_of_value_and_ram_union_p1Zero h hh hdeg hval
    (hpts_union_p1Zero_of_hbridge_and_out h hh hbridge hout)

/-! ## Axiom checks -/

#print axioms specMap_evalAt_locallyOfFinitePresentation
#print axioms chartMorphismInf_locallyOfFinitePresentation
#print axioms smoothLocus_chartInf_eq_specMap
#print axioms mem_chartInf_smoothLocus_iff
#print axioms chartInf_smoothLocus_iff_specMap
#print axioms SmoothCriterion
#print axioms smoothCriterion_iff_ram
#print axioms smoothAt_chartInf_iff
#print axioms ram_chartInf_iff_derivative_mem
#print axioms ram_eq_derivativeZeroSet_of_hcrit
#print axioms hbridge_of_smooth_criterion
#print axioms hbridge_of_hcrit
#print axioms derivativeZeroSet_eq_univ_of_derivative_eq_zero
#print axioms hbridge_of_derivative_eq_zero
#print axioms chartInf_mem_range
#print axioms branch_subset_range_of_hpts
#print axioms hpts_of_hbridge
#print axioms branch_image_ram_inter_chart0_subset
#print axioms hpts_of_hbridge_and_out
#print axioms hpts_union_p1Zero_of_hbridge_and_out
#print axioms hbH_of_value_and_ram_union_p1Zero
#print axioms hbH_of_hbridge_and_out

end LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolySmoothLocusActual
