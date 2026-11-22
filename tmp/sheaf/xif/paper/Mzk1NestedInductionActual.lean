import Mathlib
import tmp.sheaf.xif.paper.PaperScopeLemma24Actual
import tmp.sheaf.xif.paper.Mzk1Lemma24ValueDegreeDropActual
import LeanFormal.IUT.Audit.Status

/-!
# Mzk1NestedInductionActual — nested induction for [Mzk1] Lemma 2.4 (Problem C)

REAL IMPLEMENTATION of `coord/ProblemC_NestedInductionSkeleton.lean` (no sorry, no new
axiom, no `PUnit`/`True` placeholder; only `propext`, `Classical.choice`, `Quot.sound`
can appear in the axiom footprint).

Source: `papers/motizuki_corpus/text/Noncritical Belyi Maps.txt`, Lemma 2.4, lines
163-206 (algebraic nested induction part), plus `coord/OPEN-HARD-PROBLEMS.md` Problem C.

Changes against the paper's bookkeeping (user plan, as recorded in the skeleton):
1. Measure (D, N): `D = maxDeg S` is the largest degree over ℚ of a point of S and
   `N = numMax S` is the number of points attaining D; lexicographic order replaces the
   paper's nested (m(S), d(S)).
2. No Galois-stable set is used.  At each step S1 = S ∪ roots(f0) and
   S' = f0(S1) ∪ f0(roots f0'), with f0 = minpoly ℚ α0.  Every point of degree D in S'
   comes from a point of degree D in S that is not a root of f0, so N strictly drops
   when D is stable; α0 itself is a root, which removes one source.
3. Only two degree facts are needed, and both are PROVED here:
   `degQ_aeval_le` (values have no larger degree) and `degQ_critValue_lt` (critical
   values have strictly smaller degree, reusing the existing asset
   `Mzk1Lemma24ValueDegreeDropActual.valueDegreeDrop_proved`, which itself consumes
   `s3135_criticalPoint_degree_drop`).
4. No infinite Galois descent is used: everything is over the fixed field ℚ inside
   ℚ̄ = AlgebraicClosure ℚ; a rational Möbius map preserves the degree of a point
   (`degQ_moebius`).
5. The induction principle `induction_with_invariant` is proved (well-founded recursion
   on the lexicographic ℕ × ℕ measure) and instantiated on the concrete step set
   (`nested_induction_terminates`).

WHAT IS PROVED HERE (kernel-checked):
* the measure definitions and their basic degree facts (`degQ_pos`, `degQ_zero`, ...);
* `degQ_aeval_le`, `degQ_critValue_lt` (reuse of S1b), `degQ_moebius` (fractional
  linear change of variable preserves the degree over ℚ);
* `maxDeg_stepSet_le`, `numMax_stepSet_lt`, `measure_stepSet_lt` (one step of the
  induction strictly decreases (maxDeg, numMax));
* the complex-avoidance layer of the skeleton: `norm_eval_le_two_pow`,
  `three_pow_le_norm_eval`, `derivative_roots_in_disk` (Gauss-Lucas, from Mathlib),
  `eval_ne_of_disk`;
* the well-founded induction principle `induction_with_invariant`, the reachability
  relation `Reaches`, and `nested_induction_terminates` (every nonempty finite point set
  reduces in finitely many steps to a set of maximal degree ≤ 1, i.e. all-rational);
* the paper-scope assembly `paperScopeLemma24Statement_of_providers` against
  `PaperScopeLemma24Actual.PaperScopeLemma24Statement`, conditional on two EXPLICIT
  named providers `BaseCaseProvider` and `StepProvider` (the geometric map layer).

WHAT IS *NOT* DONE (exact blocker, see `nestedInductionStatus`): the two named providers
are the P¹ map layer — for the step: construct the polynomial/P¹ morphism f0 with its
pole and infinity bookkeeping, prove the critical-value containment and the backward
transport of the target; for the base: the beta-avoiding rational Belyi map.  These are
the same residues already registered in the repository (AlgebraicNestedInductionInput,
BetaAvoidingBelyiBaseInput, Mzk1Lemma24StepProviderStatement); this file supplies the
proved measure/degree engine underneath them and does not claim paper closure.
-/

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1Lemma24ValueDegreeDropActual

/-- The paper's fixed number field: ℚ̄ = AlgebraicClosure ℚ. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-! ## 1. The measure (D, N) -/

/-- Degree over ℚ of an algebraic number. -/
def degQ (α : Qbar) : ℕ := (minpoly ℚ α).natDegree

/-- Largest degree of a point of S (0 for the empty set). -/
def maxDeg (S : Finset Qbar) : ℕ := S.sup degQ

/-- Number of points of S of largest degree. -/
def numMax (S : Finset Qbar) : ℕ := (S.filter (fun α => degQ α = maxDeg S)).card

/-! ## 2. Degree facts -/

/-- Every point of ℚ̄ is integral over ℚ (ℚ̄ is algebraic over ℚ). -/
theorem isIntegral_Qbar (α : Qbar) : IsIntegral ℚ α :=
  (Algebra.isAlgebraic_iff_isIntegral.mp (AlgebraicClosure.isAlgebraic ℚ)).isIntegral α

/-- Degrees over ℚ are positive: the minimal polynomial of an algebraic number is not 1. -/
theorem degQ_pos (α : Qbar) : 0 < degQ α :=
  minpoly.natDegree_pos (isIntegral_Qbar α)

/-- The rational number 0 has degree 1 over ℚ (minpoly = X). -/
theorem degQ_zero : degQ (0 : Qbar) = 1 := by
  have h : minpoly ℚ (0 : Qbar) = Polynomial.X := by
    have h' := minpoly.eq_X_sub_C Qbar (0 : ℚ)
    simpa using h'
  rw [degQ, h]
  exact Polynomial.natDegree_X

/-- **A ℚ-polynomial value has no larger degree than the argument**: f(α) lies in ℚ(α),
so [ℚ(f(α)) : ℚ] ≤ [ℚ(α) : ℚ]. -/
theorem degQ_aeval_le (f : ℚ[X]) (α : Qbar) : degQ (aeval α f) ≤ degQ α := by
  let Fx : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ ({α} : Set Qbar)
  let Fy : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ ({(aeval α f)} : Set Qbar)
  have hmem : aeval α f ∈ Fx := by
    rw [IntermediateField.mem_adjoin_simple_iff]
    exact ⟨f, 1, by simp⟩
  have hle : Fy ≤ Fx := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hmem
  haveI : FiniteDimensional ℚ Fx :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_Qbar α)
  have hfrx : Module.finrank ℚ Fx = degQ α :=
    IntermediateField.adjoin.finrank (isIntegral_Qbar α)
  have hfry : Module.finrank ℚ Fy = degQ (aeval α f) :=
    IntermediateField.adjoin.finrank (isIntegral_Qbar (aeval α f))
  have hlefin : Module.finrank ℚ Fy ≤ Module.finrank ℚ Fx :=
    IntermediateField.finrank_le_of_le_right hle
  calc degQ (aeval α f) = Module.finrank ℚ Fy := hfry.symm
    _ ≤ Module.finrank ℚ Fx := hlefin
    _ = degQ α := hfrx

/-- **Critical values have strictly smaller degree** (paper [Mzk1] Lemma 2.4 lines
195-199): if ξ is a root of f0' for f0 = minpoly ℚ α0, then f0(ξ) has degree
< deg α0.  Reuses the existing asset `valueDegreeDrop_proved` ((S1b), PROVED in
`Mzk1Lemma24ValueDegreeDropActual`) which itself consumes
`s3135_criticalPoint_degree_drop` ((S1a)). -/
theorem degQ_critValue_lt (α0 ξ : Qbar)
    (hξ : aeval ξ (derivative (minpoly ℚ α0)) = 0) :
    degQ (aeval ξ (minpoly ℚ α0)) < degQ α0 := by
  have h0 : 1 ≤ (minpoly ℚ α0).natDegree := degQ_pos α0
  have h := valueDegreeDrop_proved α0 ξ h0 hξ
  show (minpoly ℚ (aeval ξ (minpoly ℚ α0))).natDegree < (minpoly ℚ α0).natDegree
  omega

/-- **A rational Möbius map preserves the degree**: for a fractional linear change of
variable with rational coefficients and nonvanishing determinant, ℚ(N(α)) = ℚ(α).  This
is the degree face of the Lemma 2.3 normalization (`Mzk1MoebiusP1QbarActual` is the
existing P¹ formulation). -/
theorem degQ_moebius (a b c d : ℚ) (hdet : a * d - b * c ≠ 0) (α : Qbar)
    (hden : (c : Qbar) * α + (d : Qbar) ≠ 0) :
    degQ (((a : Qbar) * α + (b : Qbar)) / ((c : Qbar) * α + (d : Qbar))) = degQ α := by
  set y : Qbar := ((a : Qbar) * α + (b : Qbar)) / ((c : Qbar) * α + (d : Qbar)) with hy
  -- y lies in ℚ(α)
  have hy_mem : y ∈ IntermediateField.adjoin ℚ ({α} : Set Qbar) := by
    rw [IntermediateField.mem_adjoin_simple_iff]
    exact ⟨Polynomial.C a * Polynomial.X + Polynomial.C b,
      Polynomial.C c * Polynomial.X + Polynomial.C d, by simp [y]⟩
  have hle1 :
      IntermediateField.adjoin ℚ ({y} : Set Qbar) ≤
        IntermediateField.adjoin ℚ ({α} : Set Qbar) := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hy_mem
  have h1 : degQ y ≤ degQ α := by
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({α} : Set Qbar)) :=
      IntermediateField.adjoin.finiteDimensional (isIntegral_Qbar α)
    have hfr1 : Module.finrank ℚ (IntermediateField.adjoin ℚ ({y} : Set Qbar)) = degQ y :=
      IntermediateField.adjoin.finrank (isIntegral_Qbar y)
    have hfr2 : Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set Qbar)) = degQ α :=
      IntermediateField.adjoin.finrank (isIntegral_Qbar α)
    have hfin := IntermediateField.finrank_le_of_le_right hle1
    calc degQ y = Module.finrank ℚ (IntermediateField.adjoin ℚ ({y} : Set Qbar)) := hfr1.symm
      _ ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set Qbar)) := hfin
      _ = degQ α := hfr2
  -- the key algebraic relation α * (c y - a) = b - d y
  have hbase : y * ((c : Qbar) * α + (d : Qbar)) = (a : Qbar) * α + (b : Qbar) := by
    rw [hy]
    exact div_mul_cancel₀ _ hden
  have hkey : y * (c : Qbar) * α = (a : Qbar) * α + (b : Qbar) - y * (d : Qbar) := by
    linear_combination hbase
  have hmul : α * ((c : Qbar) * y - (a : Qbar)) = (b : Qbar) - (d : Qbar) * y := by
    linear_combination hkey
  -- the denominator of the inverse formula is nonzero
  have hy_den : (c : Qbar) * y - (a : Qbar) ≠ 0 := by
    intro hzero
    have hcy : (c : Qbar) * y = (a : Qbar) := by linear_combination hzero
    have hyd : y * (d : Qbar) = (b : Qbar) := by
      linear_combination hkey - α * hzero
    have hq : (a : Qbar) * (d : Qbar) - (b : Qbar) * (c : Qbar) = 0 := by
      linear_combination (c : Qbar) * hyd - (d : Qbar) * hcy
    have hz : ((a * d - b * c : ℚ) : Qbar) = (0 : Qbar) := by
      push_cast
      linear_combination hq
    have hq0 : a * d - b * c = 0 := by
      have h' : ((a * d - b * c : ℚ) : Qbar) = ((0 : ℚ) : Qbar) := by
        rw [hz]
        simp
      exact Rat.cast_injective h'
    exact hdet hq0
  -- α lies in ℚ(y): α = (b - d y) / (c y - a)
  have hα_mem : α ∈ IntermediateField.adjoin ℚ ({y} : Set Qbar) := by
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨Polynomial.C b - Polynomial.C d * Polynomial.X,
      Polynomial.C c * Polynomial.X - Polynomial.C a, ?_⟩
    have hs1 : aeval y (Polynomial.C b - Polynomial.C d * Polynomial.X) =
        (b : Qbar) - (d : Qbar) * y := by
      rw [map_sub, map_mul]
      simp
    have hs2 : aeval y (Polynomial.C c * Polynomial.X - Polynomial.C a) =
        (c : Qbar) * y - (a : Qbar) := by
      rw [map_sub, map_mul]
      simp
    rw [hs1, hs2, eq_div_iff hy_den]
    exact hmul
  have hle2 :
      IntermediateField.adjoin ℚ ({α} : Set Qbar) ≤
        IntermediateField.adjoin ℚ ({y} : Set Qbar) := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hα_mem
  have h2 : degQ α ≤ degQ y := by
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({y} : Set Qbar)) :=
      IntermediateField.adjoin.finiteDimensional (isIntegral_Qbar y)
    have hfr1 : Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set Qbar)) = degQ α :=
      IntermediateField.adjoin.finrank (isIntegral_Qbar α)
    have hfr2 : Module.finrank ℚ (IntermediateField.adjoin ℚ ({y} : Set Qbar)) = degQ y :=
      IntermediateField.adjoin.finrank (isIntegral_Qbar y)
    have hfin := IntermediateField.finrank_le_of_le_right hle2
    calc degQ α = Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set Qbar)) := hfr1.symm
      _ ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ ({y} : Set Qbar)) := hfin
      _ = degQ y := hfr2
  exact le_antisymm h1 h2

/-! ## 3. One step of the induction -/

/-- Conjugates of α0: the roots of f0 = minpoly ℚ α0 in ℚ̄. -/
def conjSet (α0 : Qbar) : Finset Qbar := ((minpoly ℚ α0).aroots Qbar).toFinset

/-- Critical points of f0 = minpoly ℚ α0. -/
def critSet (α0 : Qbar) : Finset Qbar :=
  ((derivative (minpoly ℚ α0)).aroots Qbar).toFinset

/-- S' = f0(S ∪ conjugates of α0) ∪ f0(critical points of f0). -/
def stepSet (S : Finset Qbar) (α0 : Qbar) : Finset Qbar :=
  ((S ∪ conjSet α0).image (fun α => aeval α (minpoly ℚ α0))) ∪
    (critSet α0).image (fun ξ => aeval ξ (minpoly ℚ α0))

/-- The image of the minimal polynomial is nonzero: it is monic. -/
theorem minpoly_map_ne_zero (α0 : Qbar) :
    (minpoly ℚ α0).map (algebraMap ℚ Qbar) ≠ 0 :=
  ((minpoly.monic (isIntegral_Qbar α0)).map (algebraMap ℚ Qbar)).ne_zero

/-- Membership in the conjugate set: exactly the roots of f0 in ℚ̄. -/
theorem mem_conjSet_iff {α0 α : Qbar} :
    α ∈ conjSet α0 ↔ aeval α (minpoly ℚ α0) = 0 := by
  rw [conjSet, Multiset.mem_toFinset, Polynomial.mem_aroots']
  exact ⟨fun h => h.2, fun h => ⟨minpoly_map_ne_zero α0, h⟩⟩

/-- α0 is one of its own conjugates. -/
theorem self_mem_conjSet (α0 : Qbar) : α0 ∈ conjSet α0 :=
  mem_conjSet_iff.mpr (minpoly.aeval ℚ α0)

/-- Membership in the critical set gives a root of f0'. -/
theorem aeval_derivative_eq_zero_of_mem_critSet {α0 ξ : Qbar} (h : ξ ∈ critSet α0) :
    aeval ξ (derivative (minpoly ℚ α0)) = 0 :=
  ((Polynomial.mem_aroots' (p := derivative (minpoly ℚ α0)) (a := ξ) (S := Qbar)).mp
    (Multiset.mem_toFinset.mp h)).2

/-- The special value 0 is always in the step set (it is f0(α0)). -/
theorem zero_mem_stepSet (S : Finset Qbar) (α0 : Qbar) : (0 : Qbar) ∈ stepSet S α0 := by
  rw [stepSet, Finset.mem_union]
  left
  rw [Finset.mem_image]
  exact ⟨α0, Finset.mem_union.mpr (Or.inr (self_mem_conjSet α0)), minpoly.aeval ℚ α0⟩

/-- **The largest degree does not grow** (paper lines 195-203): every value f0(α) with
α ∈ S has degree ≤ deg α ≤ maxDeg S, every conjugate maps to 0 (degree 1), and every
critical value has degree < deg α0 = maxDeg S. -/
theorem maxDeg_stepSet_le (S : Finset Qbar) (α0 : Qbar) (hα0 : α0 ∈ S)
    (hmax : degQ α0 = maxDeg S) : maxDeg (stepSet S α0) ≤ maxDeg S := by
  have hD1 : 1 ≤ maxDeg S := by
    rw [← hmax]
    exact degQ_pos α0
  apply Finset.sup_le
  intro y hy
  simp only [stepSet, Finset.mem_union, Finset.mem_image] at hy
  rcases hy with ⟨α, hα, rfl⟩ | ⟨ξ, hξ, rfl⟩
  · rcases hα with hαS | hαc
    · calc degQ (aeval α (minpoly ℚ α0)) ≤ degQ α := degQ_aeval_le _ _
        _ ≤ maxDeg S := Finset.le_sup hαS
    · rw [mem_conjSet_iff.mp hαc]
      simpa [degQ_zero] using hD1
  · have hlt : degQ (aeval ξ (minpoly ℚ α0)) < maxDeg S := by
      have h := degQ_critValue_lt α0 ξ (aeval_derivative_eq_zero_of_mem_critSet hξ)
      rwa [hmax] at h
    exact hlt.le

/-- **If the largest degree stays, the number of points attaining it drops** (paper lines
195-203).  A point of degree D = maxDeg S in S' is f0(α) with α ∈ S of degree D that is
not a root of f0 (roots go to 0, of degree 1 < D), while critical values have degree
< D; α0 itself is a root, so at most numMax S - 1 sources remain, and
`Finset.card_image_le` bounds the number of images. -/
theorem numMax_stepSet_lt (S : Finset Qbar) (α0 : Qbar) (hα0 : α0 ∈ S)
    (hmax : degQ α0 = maxDeg S) (h2 : 2 ≤ degQ α0)
    (hsame : maxDeg (stepSet S α0) = maxDeg S) :
    numMax (stepSet S α0) < numMax S := by
  have hD2 : 2 ≤ maxDeg S := by
    rw [← hmax]
    exact h2
  -- every degree-D point of S' comes from a degree-D point of S different from α0
  have hsub : (stepSet S α0).filter (fun y => degQ y = maxDeg S) ⊆
      ((S.filter (fun β => degQ β = maxDeg S)).erase α0).image
        (fun β => aeval β (minpoly ℚ α0)) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyStep, hyDeg⟩ := hy
    rw [Finset.mem_image]
    simp only [stepSet, Finset.mem_union, Finset.mem_image] at hyStep
    rcases hyStep with ⟨α, hα, rfl⟩ | ⟨ξ, hξ, rfl⟩
    · rcases hα with hαS | hαc
      · -- the value f0(α), α ∈ S, of degree D
        have hdegα : degQ α ≤ maxDeg S := Finset.le_sup hαS
        have hyα : degQ (aeval α (minpoly ℚ α0)) ≤ degQ α := degQ_aeval_le _ _
        have hdegαD : degQ α = maxDeg S := by
          refine le_antisymm hdegα ?_
          rw [← hyDeg]
          exact hyα
        have hnotroot : aeval α (minpoly ℚ α0) ≠ 0 := by
          intro hz
          rw [hz, degQ_zero] at hyDeg
          omega
        have hαne : α ≠ α0 := by
          intro h
          have hzero : aeval α (minpoly ℚ α0) = 0 := by
            rw [h]
            exact minpoly.aeval ℚ α0
          exact hnotroot hzero
        refine ⟨α, ?_, rfl⟩
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨hαne, hαS, hdegαD⟩
      · -- a root of f0 maps to 0, which has degree 1 < D
        have hroot : aeval α (minpoly ℚ α0) = 0 := mem_conjSet_iff.mp hαc
        rw [hroot, degQ_zero] at hyDeg
        omega
    · -- a critical value has degree < deg α0 = D
      have hlt := degQ_critValue_lt α0 ξ (aeval_derivative_eq_zero_of_mem_critSet hξ)
      rw [hmax] at hlt
      omega
  have hcard1 : 1 ≤ (S.filter (fun β => degQ β = maxDeg S)).card := by
    have hpos : 0 < (S.filter (fun β => degQ β = maxDeg S)).card :=
      Finset.card_pos.mpr ⟨α0, by rw [Finset.mem_filter]; exact ⟨hα0, hmax⟩⟩
    omega
  have hnum : numMax (stepSet S α0) =
      ((stepSet S α0).filter (fun y => degQ y = maxDeg S)).card := by
    rw [numMax, hsame]
  calc numMax (stepSet S α0)
      = ((stepSet S α0).filter (fun y => degQ y = maxDeg S)).card := hnum
    _ ≤ (((S.filter (fun β => degQ β = maxDeg S)).erase α0).image
          (fun β => aeval β (minpoly ℚ α0))).card := Finset.card_le_card hsub
    _ ≤ ((S.filter (fun β => degQ β = maxDeg S)).erase α0).card := Finset.card_image_le
    _ = (S.filter (fun β => degQ β = maxDeg S)).card - 1 :=
        Finset.card_erase_of_mem (by rw [Finset.mem_filter]; exact ⟨hα0, hmax⟩)
    _ < (S.filter (fun β => degQ β = maxDeg S)).card := by omega
    _ = numMax S := rfl

/-- **Lexicographic decrease of the measure (D, N)** in one step. -/
theorem measure_stepSet_lt (S : Finset Qbar) (α0 : Qbar) (hα0 : α0 ∈ S)
    (hmax : degQ α0 = maxDeg S) (h2 : 2 ≤ degQ α0) :
    Prod.Lex (· < ·) (· < ·) (maxDeg (stepSet S α0), numMax (stepSet S α0))
      (maxDeg S, numMax S) := by
  have hle := maxDeg_stepSet_le S α0 hα0 hmax
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · rw [heq]
    exact Prod.Lex.right (maxDeg S) (numMax_stepSet_lt S α0 hα0 hmax h2 heq)

/-- A non-rational state admits a step that strictly decreases the measure: pick α0 of
maximal degree in S and use the step set. -/
theorem exists_stepSet_measure_lt (S : Finset Qbar) (hS : S.Nonempty) (hD : 2 ≤ maxDeg S) :
    ∃ α0 ∈ S, degQ α0 = maxDeg S ∧
      Prod.Lex (· < ·) (· < ·) (maxDeg (stepSet S α0), numMax (stepSet S α0))
        (maxDeg S, numMax S) := by
  obtain ⟨α0, hα0, hsup⟩ := Finset.exists_mem_eq_sup S hS degQ
  have hmax : degQ α0 = maxDeg S := hsup.symm
  have h2 : 2 ≤ degQ α0 := by
    rw [hmax]
    exact hD
  exact ⟨α0, hα0, hmax, measure_stepSet_lt S α0 hα0 hmax h2⟩

/-! ## 4. Avoidance over ℂ with the universal constant 4 -/

/-- Norm of a multiset product over ℂ is the product of the norms. -/
theorem norm_multiset_prod_complex (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map fun z => ‖z‖).prod := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a s ih
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

/-- A multiset of reals bounded by 2 is bounded by 2 to the cardinality. -/
theorem multiset_prod_le_two_pow (s : Multiset ℝ) (h0 : ∀ z ∈ s, 0 ≤ z)
    (h2 : ∀ z ∈ s, z ≤ 2) : s.prod ≤ 2 ^ s.card := by
  revert h0 h2
  refine Multiset.induction_on s ?_ ?_
  · intro h0 h2
    simp
  · intro a s ih h0 h2
    have ha2 : a ≤ 2 := h2 a (Multiset.mem_cons_self a s)
    have hs0 : ∀ z ∈ s, 0 ≤ z := fun z hz => h0 z (Multiset.mem_cons_of_mem hz)
    have hs2 : ∀ z ∈ s, z ≤ 2 := fun z hz => h2 z (Multiset.mem_cons_of_mem hz)
    have hih : s.prod ≤ 2 ^ s.card := ih hs0 hs2
    have hstep : a * s.prod ≤ 2 * 2 ^ s.card :=
      mul_le_mul ha2 hih (Multiset.prod_nonneg hs0) (by norm_num)
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc a * s.prod ≤ 2 * 2 ^ s.card := hstep
      _ = 2 ^ s.card * 2 := by ring

/-- A multiset of reals bounded below by 3 is bounded below by 3 to the cardinality. -/
theorem three_pow_le_multiset_prod (s : Multiset ℝ) (h3 : ∀ z ∈ s, 3 ≤ z) :
    (3 : ℝ) ^ s.card ≤ s.prod := by
  revert h3
  refine Multiset.induction_on s ?_ ?_
  · intro h3
    simp
  · intro a s ih h3
    have ha3 : 3 ≤ a := h3 a (Multiset.mem_cons_self a s)
    have hs3 : ∀ z ∈ s, 3 ≤ z := fun z hz => h3 z (Multiset.mem_cons_of_mem hz)
    have hih : (3 : ℝ) ^ s.card ≤ s.prod := ih hs3
    have hstep : 3 * 3 ^ s.card ≤ a * s.prod :=
      mul_le_mul ha3 hih (by positivity) (by linarith)
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc 3 ^ s.card * 3 = 3 * 3 ^ s.card := by ring
      _ ≤ a * s.prod := hstep

/-- **If all roots are in the closed unit disk, then |f| ≤ 2^d on the disk**: product
form over the roots, each factor ‖x - a‖ ≤ ‖x‖ + ‖a‖ ≤ 2. -/
theorem norm_eval_le_two_pow (f : ℂ[X]) (hf : f.Monic)
    (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖f.eval x‖ ≤ 2 ^ f.natDegree := by
  rw [Splits.eval_eq_prod_roots_of_monic (IsAlgClosed.splits f) hf x]
  have hbound : ∀ z ∈ f.roots.map (fun a => ‖x - a‖), 0 ≤ z ∧ z ≤ 2 := by
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    refine ⟨norm_nonneg _, ?_⟩
    calc ‖x - a‖ ≤ ‖x‖ + ‖a‖ := norm_sub_le x a
      _ ≤ 2 := by linarith [hroots a ha, hx]
  have hprod := multiset_prod_le_two_pow (f.roots.map fun a => ‖x - a‖)
    (fun z hz => (hbound z hz).1) (fun z hz => (hbound z hz).2)
  calc ‖(f.roots.map (fun a => x - a)).prod‖
      = (f.roots.map fun a => ‖x - a‖).prod := by
        rw [norm_multiset_prod_complex, Multiset.map_map]
        rfl
    _ ≤ 2 ^ (f.roots.map fun a => ‖x - a‖).card := hprod
    _ = 2 ^ f.natDegree := by
        rw [Multiset.card_map, ← Splits.natDegree_eq_card_roots (IsAlgClosed.splits f)]

/-- **If all roots are in the closed unit disk, then |f(β)| ≥ 3^d for ‖β‖ ≥ 4**:
each factor satisfies ‖β - a‖ ≥ ‖β‖ - ‖a‖ ≥ 3. -/
theorem three_pow_le_norm_eval (f : ℂ[X]) (hf : f.Monic)
    (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) {β : ℂ} (hβ : 4 ≤ ‖β‖) :
    (3 : ℝ) ^ f.natDegree ≤ ‖f.eval β‖ := by
  rw [Splits.eval_eq_prod_roots_of_monic (IsAlgClosed.splits f) hf β]
  have hbound : ∀ z ∈ f.roots.map (fun a => ‖β - a‖), 3 ≤ z := by
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have h1 : ‖β‖ - ‖a‖ ≤ ‖β - a‖ := norm_sub_norm_le β a
    have h2 : ‖a‖ ≤ 1 := hroots a ha
    linarith
  have hprod := three_pow_le_multiset_prod (f.roots.map fun a => ‖β - a‖) hbound
  calc (3 : ℝ) ^ f.natDegree
      = 3 ^ (f.roots.map fun a => ‖β - a‖).card := by
        rw [Multiset.card_map, Splits.natDegree_eq_card_roots (IsAlgClosed.splits f)]
    _ ≤ (f.roots.map fun a => ‖β - a‖).prod := hprod
    _ = ‖(f.roots.map (fun a => β - a)).prod‖ := by
        rw [norm_multiset_prod_complex, Multiset.map_map]
        rfl

/-- **Gauss-Lucas** (Mathlib `Polynomial.rootSet_derivative_subset_convexHull_rootSet`):
the critical points of f lie in the convex hull of the roots, hence in the same disk if
all roots are in the closed unit disk. -/
theorem derivative_roots_in_disk (f : ℂ[X]) (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) :
    ∀ ξ ∈ f.derivative.roots, ‖ξ‖ ≤ 1 := by
  intro ξ hξ
  by_cases hf0 : f = 0
  · subst hf0
    simp at hξ
  by_cases hdeg0 : f.natDegree = 0
  · have hC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hder : f.derivative = 0 := by
      rw [hC]
      simp
    rw [hder] at hξ
    simp at hξ
  · have hpos : 0 < f.degree := by
      rw [Polynomial.degree_eq_natDegree hf0]
      exact_mod_cast Nat.pos_of_ne_zero hdeg0
    have hderne : f.derivative ≠ 0 := by
      intro h
      rw [h] at hξ
      simp at hξ
    have hroot : ξ ∈ (f.derivative).rootSet ℂ := by
      rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
      exact ⟨hderne, (Polynomial.mem_roots hderne).mp hξ⟩
    have hball : f.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 1 := by
      intro a ha
      rw [Polynomial.mem_rootSet] at ha
      obtain ⟨hane, haeval⟩ := ha
      have haeval' : f.eval a = 0 := by
        rwa [Polynomial.coe_aeval_eq_eval] at haeval
      have hamem : a ∈ f.roots := (Polynomial.mem_roots hf0).mpr haeval'
      have ha1 : ‖a‖ ≤ 1 := hroots a hamem
      simpa [Metric.mem_closedBall, dist_zero_right] using ha1
    have hconv : ξ ∈ convexHull ℝ (f.rootSet ℂ) :=
      Polynomial.rootSet_derivative_subset_convexHull_rootSet hpos hroot
    have hsub := convexHull_min hball (convex_closedBall (0 : ℂ) 1)
    have := hsub hconv
    simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- **Avoidance**: a monic f of positive degree with roots in the closed unit disk takes
at β (‖β‖ ≥ 4) a value different from every value on the closed unit disk (in particular
from all values f(γ) with ‖γ‖ ≤ 1, hence from f(S) and from all critical values by
Gauss-Lucas). -/
theorem eval_ne_of_disk (f : ℂ[X]) (hf : f.Monic) (hdeg : 1 ≤ f.natDegree)
    (hroots : ∀ a ∈ f.roots, ‖a‖ ≤ 1) {β γ : ℂ} (hβ : 4 ≤ ‖β‖) (hγ : ‖γ‖ ≤ 1) :
    f.eval β ≠ f.eval γ := by
  intro heq
  have h1 : (3 : ℝ) ^ f.natDegree ≤ ‖f.eval β‖ := three_pow_le_norm_eval f hf hroots hβ
  have h2 : ‖f.eval γ‖ ≤ 2 ^ f.natDegree := norm_eval_le_two_pow f hf hroots hγ
  have h3 : (3 : ℝ) ^ f.natDegree ≤ 2 ^ f.natDegree := by
    calc (3 : ℝ) ^ f.natDegree ≤ ‖f.eval β‖ := h1
      _ = ‖f.eval γ‖ := by rw [heq]
      _ ≤ 2 ^ f.natDegree := h2
  have hlt : (2 : ℝ) ^ f.natDegree < 3 ^ f.natDegree :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith

/-! ## 5. Induction principle with an invariant and a fixed measure -/

/-- **Well-founded induction on a lexicographic ℕ × ℕ measure, restricted to admissible
states.**  `base` is asked only where the first component is at most 1 (all-rational
states); `step` only on admissible states with first component > 1 and must return an
admissible state of strictly smaller measure together with the backward goal transport. -/
theorem induction_with_invariant {σ : Type*} (μ : σ → ℕ × ℕ) (Inv Goal : σ → Prop)
    (base : ∀ s, Inv s → (μ s).1 ≤ 1 → Goal s)
    (step : ∀ s, Inv s → 1 < (μ s).1 →
      ∃ s', Inv s' ∧ Prod.Lex (· < ·) (· < ·) (μ s') (μ s) ∧ (Goal s' → Goal s)) :
    ∀ s, Inv s → Goal s := by
  have hwf : WellFounded (InvImage (Prod.Lex (· < ·) (· < ·)) μ) :=
    InvImage.wf μ (WellFounded.prod_lex (wellFounded_lt (α := ℕ)) (wellFounded_lt (α := ℕ)))
  intro s
  refine hwf.induction (C := fun s => Inv s → Goal s) s ?_
  intro x ih hx
  by_cases hle : (μ x).1 ≤ 1
  · exact base x hx hle
  · have hgt : 1 < (μ x).1 := by omega
    obtain ⟨x', hInv', hlt, hgoal⟩ := step x hx hgt
    exact hgoal (ih x' hlt hInv')

/-! ### Reachability and termination of the concrete nested induction -/

/-- Reachability of a point set by finitely many step-set reductions. -/
inductive Reaches : Finset Qbar → Finset Qbar → Prop where
  | refl (S : Finset Qbar) : Reaches S S
  | step {S U : Finset Qbar} (α0 : Qbar) (hα0 : α0 ∈ S)
      (h : Reaches (stepSet S α0) U) : Reaches S U

/-- **The nested induction terminates with an all-rational state**: every nonempty finite
set of algebraic points can be replaced, in finitely many steps of the form
S ↦ f0(S ∪ conjugates) ∪ f0(critical points), by a set whose maximal degree is ≤ 1.
This is the paper's recursion (lines 195-206) with the measure (maxDeg, numMax) and
WITHOUT Galois-stable sets. -/
theorem nested_induction_terminates (S : Finset Qbar) (hS : S.Nonempty) :
    ∃ T : Finset Qbar, Reaches S T ∧ maxDeg T ≤ 1 := by
  refine induction_with_invariant (μ := fun S => (maxDeg S, numMax S))
    (Inv := fun S => S.Nonempty)
    (Goal := fun S => ∃ T : Finset Qbar, Reaches S T ∧ maxDeg T ≤ 1) ?_ ?_ S hS
  · intro S hne hsmall
    exact ⟨S, Reaches.refl S, hsmall⟩
  · intro S hne hbig
    obtain ⟨α0, hα0, hmax⟩ := Finset.exists_mem_eq_sup S hne degQ
    have h2 : 2 ≤ degQ α0 := by
      have h : 2 ≤ S.sup degQ := Nat.succ_le_of_lt hbig
      rwa [hmax] at h
    refine ⟨stepSet S α0, ⟨0, zero_mem_stepSet S α0⟩,
      measure_stepSet_lt S α0 hα0 hmax.symm h2, ?_⟩
    rintro ⟨T, hReach, hmaxT⟩
    exact ⟨T, Reaches.step α0 hα0 hReach, hmaxT⟩

/-! ## 6. Paper-scope assembly against `PaperScopeLemma24Statement` -/

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual

/-- Degree over ℚ of a point of P¹(ℚ̄): a finite point has its degree over ℚ, while the
point at infinity is ℚ-rational, i.e. of degree 1. -/
def degP (p : P1Point (AlgebraicClosure ℚ)) : ℕ :=
  match p with
  | none => 1
  | some z => degQ z

/-- Largest degree of a point of a finite subset of P¹(ℚ̄). -/
def maxDegP (S : Finset (P1Point (AlgebraicClosure ℚ))) : ℕ := S.sup degP

/-- Number of points of a finite subset of P¹(ℚ̄) of largest degree. -/
def numMaxP (S : Finset (P1Point (AlgebraicClosure ℚ))) : ℕ :=
  (S.filter (fun p => degP p = maxDegP S)).card

/-- **Named input (base case)**: the paper's Lemma 2.4 target holds for states in which
every point has degree ≤ 1 (all points rational).  This is the beta-avoiding rational
Belyi/base layer (`Mzk1Lemma24BaseCaseActual`, `Mzk1Lemma24BaseProviderActual`); it is
NOT asserted here. -/
def BaseCaseProvider : Prop :=
  ∀ (S : Finset (P1Point (AlgebraicClosure ℚ))) (β : P1Point (AlgebraicClosure ℚ)),
    β ∉ S → maxDegP S ≤ 1 → PaperScopeLemma24Target S β

/-- **Named input (induction step / map layer)**: from a state with a point of degree ≥ 2
one can pass to a new state S' that still avoids β, has strictly smaller (maxDegP,
numMaxP), and from which the paper target transports backwards to S.  The existence of
S' with the asserted measure decrease and transport is exactly the P¹ map layer
(f0 with its pole/infinity bookkeeping, critical-value containment, composition of the
P¹ morphisms).  The *measure* decrease for the finite step set is proved above
(`measure_stepSet_lt`); only the geometric construction/transport is named here. -/
def StepProvider : Prop :=
  ∀ (S : Finset (P1Point (AlgebraicClosure ℚ))) (β : P1Point (AlgebraicClosure ℚ)),
    β ∉ S → 1 < maxDegP S →
      ∃ S' : Finset (P1Point (AlgebraicClosure ℚ)),
        β ∉ S' ∧
          Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S) ∧
            (PaperScopeLemma24Target S' β → PaperScopeLemma24Target S β)

/-- **Conditional assembly of the paper-scope Lemma 2.4**: the two named providers give
`PaperScopeLemma24Actual.PaperScopeLemma24Statement`, by the proved well-founded
lexicographic induction principle.  No paper closure is claimed: both providers are
explicit hypotheses of this theorem. -/
theorem paperScopeLemma24Statement_of_providers (hbase : BaseCaseProvider)
    (hstep : StepProvider) : PaperScopeLemma24Statement := by
  intro S β hβ
  exact induction_with_invariant
    (μ := fun S : Finset (P1Point (AlgebraicClosure ℚ)) => (maxDegP S, numMaxP S))
    (Inv := fun S => β ∉ S)
    (Goal := fun S => PaperScopeLemma24Target S β)
    (fun S hS hle => hbase S β hS hle)
    (fun S hS hgt => hstep S β hS hgt)
    S hβ

/-- The P¹ measure of a set of finite points agrees with the ℚ-degree measure used in the
step lemmas. -/
theorem maxDegP_image_ofFinite (S : Finset Qbar) :
    maxDegP (S.image (fun z => P1Point.ofFinite z)) = maxDeg S := by
  rw [maxDegP, Finset.sup_image]
  rfl

/-- The P¹ maximal-count of a set of finite points agrees with `numMax`. -/
theorem numMaxP_image_ofFinite (S : Finset Qbar) :
    numMaxP (S.image (fun z => P1Point.ofFinite z)) = numMax S := by
  rw [numMaxP, maxDegP_image_ofFinite, numMax]
  have h : (S.image (fun z => P1Point.ofFinite z)).filter (fun p => degP p = maxDeg S) =
      (S.filter (fun z => degQ z = maxDeg S)).image (fun z => P1Point.ofFinite z) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hpdeg⟩
      exact ⟨z, ⟨hz, hpdeg⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzdeg⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hzdeg⟩
  rw [h]
  exact Finset.card_image_of_injective _ (fun x y hxy => Option.some.inj hxy)

/-! ## 7. Ledger -/

/-- Rows: (component, evidence, status). -/
def nestedInductionRows : List (String × String × String) :=
  [ ("degQ, maxDeg, numMax", "definitions", "DEFINED"),
    ("degQ_pos / degQ_zero", "minpoly.natDegree_pos / minpoly.eq_X_sub_C", "PROVED"),
    ("degQ_aeval_le", "IntermediateField adjoin finrank tower", "PROVED"),
    ("degQ_critValue_lt", "reuse valueDegreeDrop_proved (S1b) + s3135_criticalPoint_degree_drop", "PROVED"),
    ("degQ_moebius", "explicit rational inverse formula (b - d y)/(c y - a)", "PROVED"),
    ("maxDeg_stepSet_le", "degQ_aeval_le + degQ_critValue_lt + degQ_zero", "PROVED"),
    ("numMax_stepSet_lt", "Finset.card_le_card + card_image_le + card_erase_of_mem", "PROVED"),
    ("measure_stepSet_lt", "maxDeg_stepSet_le + numMax_stepSet_lt (Prod.Lex)", "PROVED"),
    ("norm_eval_le_two_pow / three_pow_le_norm_eval", "product form over roots (Splits) + norm bounds", "PROVED"),
    ("derivative_roots_in_disk", "Mathlib Gauss-Lucas + convexity of the closed ball", "PROVED"),
    ("eval_ne_of_disk", "2^d < 3^d for d >= 1", "PROVED"),
    ("induction_with_invariant", "WellFounded.induction on InvImage (Prod.Lex) mu", "PROVED"),
    ("nested_induction_terminates", "induction_with_invariant + measure_stepSet_lt + Reaches", "PROVED"),
    ("maxDegP/numMaxP bridge", "Finset.sup_image + filter/image card", "PROVED"),
    ("BaseCaseProvider (paper base case)", "DISCHARGED: Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved (identity polynomial, unconditional)", "PROVED"),
    ("StepProvider (P1 map layer / transport)", "named input (f0 morphism, CV containment, pole/infinity bookkeeping)", "NAMED"),
    ("paperScopeLemma24Statement_of_providers", "assembly of the two providers; base now PROVED, StepProvider named", "CONDITIONAL (StepProvider named)") ]

theorem nestedInductionRows_length : nestedInductionRows.length = 17 := rfl

/-- Status: the measure/degree engine of Problem C is PROVED; the geometric map layer
remains the two explicit named providers.  No paper closure claim; no new axioms. -/
def nestedInductionStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.nested-induction-problemC"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 163-206; coord/OPEN-HARD-PROBLEMS.md Problem C"
    status := Audit.VerificationStatus.interface
    note := "PROVED (new, kernel-checked): degree facts degQ_aeval_le, degQ_critValue_lt (reuses valueDegreeDrop_proved), degQ_moebius; step lemmas maxDeg_stepSet_le, numMax_stepSet_lt, measure_stepSet_lt for S' = f0(S union conj) union f0(crit); complex avoidance norm_eval_le_two_pow, three_pow_le_norm_eval, derivative_roots_in_disk (Mathlib Gauss-Lucas), eval_ne_of_disk; the lexicographic well-founded induction principle induction_with_invariant; termination nested_induction_terminates over the reachability relation Reaches (fixed measure (maxDeg, numMax), NO Galois-stable sets, NO infinite Galois descent); P1 measure bridge maxDegP/numMaxP; conditional assembly paperScopeLemma24Statement_of_providers against PaperScopeLemma24Actual.PaperScopeLemma24Statement. NAMED REMAINING (the blocker): StepProvider only — BaseCaseProvider is now DISCHARGED by Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved (identity polynomial, unconditional); formerly named StepProvider (P1 map layer: construction of f0-morphism with pole/infinity bookkeeping, critical-value containment, backward transport), i.e. the same residues registered as BetaAvoidingBelyiBaseInput / AlgebraicNestedInductionInput / Mzk1Lemma24StepProviderStatement. No sorry, no new axiom, no True/PUnit placeholder; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.step-provider", "MZK1.lemma24.paper-scope" ]
    sorryItems :=
      [ "StepProvider (named: P1 map layer with measure decrease and target transport)" ] }

#check degQ_aeval_le
#check degQ_critValue_lt
#check degQ_moebius
#check maxDeg_stepSet_le
#check numMax_stepSet_lt
#check measure_stepSet_lt
#check norm_eval_le_two_pow
#check three_pow_le_norm_eval
#check derivative_roots_in_disk
#check eval_ne_of_disk
#check induction_with_invariant
#check nested_induction_terminates
#check paperScopeLemma24Statement_of_providers

end LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
end
-- pin-bump-a411
-- ledger-discharge-bump
