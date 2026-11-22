import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues
import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: CV composition/base Good -> hits ported tauceti_belyi_core CriticalValues:140 criticalValues_comp_subset (PROVED) + Mzk1PolyMapActual -> REUSE (minimal green helpers; TODO rows for remaining proofs).

# Mzk1Lemma22FullShapeHelpersActual — minimal green helpers for the flattened Q[X] Good induction

MINIMAL GREEN VERSION per Lead. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22FullShapeHelpersActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual

/-- **(1) Critical-value composition law over C** (ported theorem instantiation). -/
theorem critValues_comp_subset (p q : ℚ[X]) :
    (p.comp q).criticalValues ℂ ⊆
      (fun y => Polynomial.aeval y p) '' q.criticalValues ℂ ∪ p.criticalValues ℂ :=
  Polynomial.criticalValues_comp_subset p q

/-- **(1') Union form:** CV(psi o phi) subset CV psi union psi(CV phi). -/
theorem critValues_comp_subset_union (p q : ℚ[X]) :
    (p.comp q).criticalValues ℂ ⊆
      p.criticalValues ℂ ∪ (fun y => Polynomial.aeval y p) '' q.criticalValues ℂ := by
  refine Set.Subset.trans (critValues_comp_subset p q) ?_
  intro x hx
  rcases hx with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **(2) Base Good data:** f = C c * X with c != 0 and separation c*b >= 2. -/
structure BaseGoodData where
  c : ℚ
  b : ℚ
  hc : c ≠ 0
  hb : 0 < b
  hcb : 2 ≤ c * b

/-- The base polynomial f = C c * X. -/
def baseGoodPoly (c : ℚ) : ℚ[X] := Polynomial.C c * Polynomial.X

/-- natDegree of the base polynomial: 1. -/
theorem baseGood_natDegree {c : ℚ} (hc : c ≠ 0) : (baseGoodPoly c).natDegree = 1 := by
  unfold baseGoodPoly
  exact Polynomial.natDegree_C_mul_X c hc

/-- Derivative of the base polynomial: the constant c. -/
theorem baseGood_derivative (c : ℚ) : (baseGoodPoly c).derivative = Polynomial.C c := by
  unfold baseGoodPoly
  rw [Polynomial.derivative_C_mul_X]

/-- **(3) C-point critical-value predicate** (matches stepxi CPointCriticalValuesIn01). -/
def CritIn01 (f : ℚ[X]) : Prop :=
  ∀ z : ℂ, (Polynomial.derivative (f.map (algebraMap ℚ ℂ))).eval z = 0 →
    (f.map (algebraMap ℚ ℂ)).eval z = 0 ∨ (f.map (algebraMap ℚ ℂ)).eval z = 1

/-- Helper row record. -/
def fullShapeHelperRows : List (String × String × String) :=
  [ ("CV composition law over C", "A", "PROVED critValues_comp_subset / _union (REUSE ported)")
  , ("base Good natDegree/derivative", "A", "PROVED baseGood_natDegree / baseGood_derivative; BaseGoodData defined")
  , ("C-point predicate CritIn01", "A", "DEFINED")
  , ("base Good CV=empty / C-unramified", "TODO", "NAMED TODO")
  , ("CritIn01 bridge + Belyi instantiation", "TODO", "NAMED TODO")
  , ("restated-2.4 CV composition law", "A", "PROVED cvCompositionLaw (CVCompositionLawStatement)")
  , ("restated-2.4 special-set preservation", "A", "PROVED specialSetPreservation (SpecialSetPreservationStatement)") ]

theorem fullShapeHelperRows_length : fullShapeHelperRows.length = 7 := rfl

#check critValues_comp_subset
#check critValues_comp_subset_union
#check baseGood_natDegree
#check baseGood_derivative
#check CritIn01
#check cvCompositionLaw
#check specialSetPreservation
#check fullShapeHelperRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22FullShapeHelpersActual
end