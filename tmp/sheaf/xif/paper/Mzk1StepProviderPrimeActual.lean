import tmp.sheaf.xif.paper.Mzk1NestedInductionActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

/-! # Mzk1StepProviderPrimeActual — StepProvider' (beta' = f0(beta)) real layer, first batch

STEP 0 prior-art: Mzk1NestedInductionActual (StepProvider, maxDegP, numMaxP,
PaperScopeLemma24Target, conjSet, critSet, measure_stepSet_lt), Mzk1F0StepGeometryActual
(f0Map, f0Poly, f0CritValues, f0StepTarget, f0CritValue_deg_le), Mzk1P1MorphismInterfaceActual.

A424 approved restatement: the fixed-beta StepProvider field beta notin S' is a spec defect
(f0(S) may contain beta); the paper's step transforms beta' = f0(beta), and the Target
definition holds for ANY beta'.  This file defines StepProvider' and proves the first
provable fields (f1 max-degree point selection; f2 S' construction with infinity
bookkeeping).  f4 P1-measure transfer and f5 composition transport are the next batches;
the fixed-beta equivalence needs a NAMED alpha0/Galois choice argument (not asserted).
No closure claim. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open scoped Classical

/-- A point of S with maximal degree over Q (must be finite when maxDegP S > 1). -/
theorem exists_maxDegP_finite (S : Finset (P1Point Qbar)) (hS : 1 < maxDegP S) :
    ∃ alpha0 : Qbar, P1Point.ofFinite alpha0 ∈ S ∧ degQ alpha0 = maxDegP S := by
  have hne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | h
    · simp [maxDegP] at hS
    · exact h
  obtain ⟨p, hpS, hpdeg⟩ := Finset.exists_mem_eq_sup (s := S) hne (f := degP)
  have hpdeg' : degP p = maxDegP S := hpdeg.symm
  cases p with
  | none =>
      -- degP infinity = 1, contradicting 1 < maxDegP S
      have h1 : degP (none : P1Point Qbar) = 1 := rfl
      rw [h1] at hpdeg'
      omega
  | some alpha0 =>
      exact ⟨alpha0, hpS, hpdeg'⟩

/-- f0-map of a finite point. -/
def f0MapAt (alpha0 : Qbar) (x : Qbar) : P1Point Qbar :=
  f0Map alpha0 (P1Point.ofFinite x)

theorem f0MapAt_eq (alpha0 x : Qbar) :
    f0MapAt alpha0 x = P1Point.ofFinite (aeval x (f0Poly alpha0)) := rfl

/-- The P1 step target S' = f0(S union conjugates) union f0(critical points). -/
def stepSetP1 (S : Finset (P1Point Qbar)) (alpha0 : Qbar) : Finset (P1Point Qbar) :=
  (S ∪ (conjSet alpha0).image (fun x => P1Point.ofFinite x)).image (f0Map alpha0) ∪
    (critSet alpha0).image (fun x => P1Point.ofFinite (aeval x (f0Poly alpha0)))

theorem mem_stepSetP1_of_mem {S : Finset (P1Point Qbar)} {alpha0 : Qbar}
    {p : P1Point Qbar} (hp : p ∈ S) : f0Map alpha0 p ∈ stepSetP1 S alpha0 := by
  unfold stepSetP1
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, Finset.mem_union_left _ hp, rfl⟩)

theorem mem_stepSetP1_of_conj {S : Finset (P1Point Qbar)} {alpha0 x : Qbar}
    (hx : x ∈ conjSet alpha0) :
    f0Map alpha0 (P1Point.ofFinite x) ∈ stepSetP1 S alpha0 := by
  unfold stepSetP1
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨P1Point.ofFinite x, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩), rfl⟩)

theorem mem_stepSetP1_of_crit {S : Finset (P1Point Qbar)} {alpha0 x : Qbar}
    (hx : x ∈ critSet alpha0) :
    P1Point.ofFinite (aeval x (f0Poly alpha0)) ∈ stepSetP1 S alpha0 := by
  unfold stepSetP1
  exact Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)




/-- **StepProvider' (A424 restated):** the paper's one-step transfer with beta' = f0(beta). -/
def StepProvider' : Prop :=
  forall (S : Finset (P1Point Qbar)) (beta : P1Point Qbar),
    beta ∉ S -> 1 < maxDegP S ->
      ∃ (alpha0 : Qbar) (S' : Finset (P1Point Qbar)) (beta' : P1Point Qbar),
        P1Point.ofFinite alpha0 ∈ S ∧
          degQ alpha0 = maxDegP S ∧
            beta' = f0Map alpha0 beta ∧
              Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S) ∧
                (PaperScopeLemma24Target S' beta' -> PaperScopeLemma24Target S beta)

/-- NAMED INPUT: fixed-beta equivalence needs the alpha0/Galois choice argument (paper's
exclusion of finitely many bad conjugacy classes); registered, NOT asserted. -/
def StepProviderFixedBetaChoiceInput : Prop :=
  forall (S : Finset (P1Point Qbar)) (beta : P1Point Qbar),
    beta ∉ S -> 1 < maxDegP S ->
      ∃ (alpha0 : Qbar) (S' : Finset (P1Point Qbar)),
        P1Point.ofFinite alpha0 ∈ S ∧ degQ alpha0 = maxDegP S ∧ beta ∉ S' ∧
          Prod.Lex (· < ·) (· < ·) (maxDegP S', numMaxP S') (maxDegP S, numMaxP S) ∧
            (PaperScopeLemma24Target S' beta -> PaperScopeLemma24Target S beta)


/-- Rows: first batch status + remaining fields. -/
def stepProviderPrimeRows : List (String × String × String) :=
  [ ("f1 max-degree point selection", "PROVED", "exists_maxDegP_finite")
  , ("f2 S' construction (P1, infinity bookkeeping)", "DEFINED + PROVED membership", "stepSetP1 + mem_stepSetP1_of_mem/_of_conj/_of_crit")
  , ("f5 composition transport Target S' beta' -> Target S beta", "NEXT (provable via f' comp f0 + CV chain rule)", "derivative_comp/aeval_comp + Target definition")
  , ("StepProvider' definition", "DEFINED", "StepProviderPrimeActual.StepProvider'")
  , ("fixed-beta equivalence", "NAMED INPUT", "StepProviderFixedBetaChoiceInput (alpha0/Galois choice; not asserted)")
  , ("base case provider", "PROVED elsewhere", "Mzk1NestedInductionBaseCaseActual.baseCaseProvider_proved")
  , ("closure", "NOT CLAIMED", "gate NOT PASSED; binding HOLD") ]

theorem stepProviderPrimeRows_length : stepProviderPrimeRows.length = 7 := rfl

#check exists_maxDegP_finite
#check stepSetP1
#check StepProvider'
#check StepProviderFixedBetaChoiceInput

end LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
end
