import LeanFormal.IUT.Foundations.Geometry.TateInverseJUniformization

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1508FiveTateParameterActual

local instance fivePrimeFact1508 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The actual q-series Tate parameter at l = 5: q = 5. -/
noncomputable def concreteFiveTateParameter :
    ConcreteTateParameter fivePrimeLabelInverseJ :=
  letI : Fact (Nat.Prime fivePrimeLabelInverseJ.value) :=
    ⟨fivePrimeLabelInverseJ.prime⟩
  ConcreteTateParameter.canonical fivePrimeLabelInverseJ

@[simp] theorem concreteFiveTateParameter_q :
    (concreteFiveTateParameter).q = (5 : ℚ_[5]) := by
  unfold concreteFiveTateParameter
  rw [ConcreteTateParameter.canonical_q, fivePrimeLabelInverseJ_value]

theorem concreteFiveTateParameter_norm :
    ‖(concreteFiveTateParameter).q‖ = (5 : Real)⁻¹ := by
  rw [concreteFiveTateParameter_q]
  exact Padic.norm_p

theorem concreteFiveTateParameter_norm_lt_one :
    ‖(concreteFiveTateParameter).q‖ < 1 := by
  rw [concreteFiveTateParameter_norm]
  norm_num

theorem concreteFiveTateParameter_ne_zero :
    (concreteFiveTateParameter).q ≠ 0 :=
  (concreteFiveTateParameter).q_ne_zero

theorem concreteFiveTateParameter_eq_inverseJCandidate :
    (concreteFiveTateParameter).q = inverseJCandidateFive := by
  rw [concreteFiveTateParameter_q, inverseJCandidateFive_eq]

theorem concreteFiveTateParameter_curve :
    (concreteFiveTateParameter).curve =
      TateCurve.weierstrassCurve ℚ_[5] (5 : ℚ_[5]) := by
  rw [ConcreteTateParameter.canonical_curve_eq, concreteFiveTateParameter_q]

theorem concreteFiveTateParameter_j_norm :
    ‖TateCurvePadic.tateJInvariant fivePrimeLabelInverseJ‖ = (5 : Real) :=
  tateJInvariant_five_norm

#print axioms concreteFiveTateParameter_norm
#print axioms concreteFiveTateParameter_eq_inverseJCandidate
#print axioms concreteFiveTateParameter_j_norm

end LeanFormal.IUT.XiFPaper.S1508FiveTateParameterActual
end
