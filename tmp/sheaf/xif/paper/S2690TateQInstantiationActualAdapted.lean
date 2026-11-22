import LeanFormal.IUT.Foundations.PAdicAnalytic.TateInverseJFinal
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurvePadic
import LeanFormal.IUT.Foundations.Geometry.TateInverseJUniformization

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2690TateQInstantiationActualAdapted

local instance fivePrimeFact2690 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Actual existence of the inverse-j Tate parameter at t = -10805 in Q_5. -/
theorem S2690TateQ_exists :
    ∃ q : concreteLocalField,
      tateHK (K := concreteLocalField) q = (-10805 : concreteLocalField) ∧
      tateJK (K := concreteLocalField) q = (-10805 : concreteLocalField)⁻¹ ∧
      ‖q‖ < 1 := by
  apply exists_tateHK_eq_and_tateJK_eq_inv (K := concreteLocalField)
  · intro n
    have hcast : ((n : ℤ) : concreteLocalField) = (n : concreteLocalField) := by
      norm_num
    rw [← hcast]
    exact Padic.norm_int_le_one (p := 5) (n : ℤ)
  · change ‖(1728 : ℚ_[5])‖ = 1
    rw [Padic.norm_natCast_eq_one_iff (p := 5) (n := 1728)]
    norm_num
  · norm_num
  · change ‖((-10805 : ℤ) : ℚ_[5])‖ < 1
    rw [Padic.norm_intCast_lt_one_iff (p := 5) (k := -10805)]
    norm_num

/-- The actual q_Tate parameter, chosen from the closed inverse-j theorem. -/
noncomputable def S2690TateQ : concreteLocalField :=
  Classical.choose S2690TateQ_exists

theorem S2690TateQ_tateHK :
    tateHK (K := concreteLocalField) S2690TateQ = (-10805 : concreteLocalField) :=
  (Classical.choose_spec S2690TateQ_exists).1

theorem S2690TateQ_tateJK :
    tateJK (K := concreteLocalField) S2690TateQ =
      (-10805 : concreteLocalField)⁻¹ :=
  (Classical.choice_spec S2690TateQ_exists).2.1

theorem S2690TateQ_norm_lt_one : ‖S2690TateQ‖ < 1 :=
  (Classical.choice_spec S2690TateQ_exists).2.2

theorem S2690TateQ_ne_zero : S2690TateQ ≠ 0 := by
  intro h
  have hnorm := S2690TateQ_norm_lt_one
  rw [h] at hnorm
  norm_num at hnorm

/-- The paper q = 5 as an element of the same local field. -/
noncomputable def S2690PaperQ : concreteLocalField := (5 : concreteLocalField)

theorem S2690PaperQ_norm : ‖S2690PaperQ‖ = (5 : Real)⁻¹ := by
  unfold S2690PaperQ
  exact Padic.norm_p (p := 5)

theorem S2690PaperQ_eq_inverseJCandidate :
    S2690PaperQ = inverseJCandidateFive :=
  rfl

/-- Exact necessary condition for paper q = 5 to equal q_Tate: its tateJK
value must be -1/10805.  This is a real condition on the q-series, not assumed. -/
theorem S2690PaperQ_eq_TateQ_implies_tateJK
    (h : S2690PaperQ = S2690TateQ) :
    tateJK (K := concreteLocalField) S2690PaperQ =
      (-10805 : concreteLocalField)⁻¹ := by
  rw [h, S2690TateQ_tateJK]

/-- The exact unresolved comparison condition. -/
def S2690PaperQ_tateJK_condition : Prop :=
  tateJK (K := concreteLocalField) S2690PaperQ =
    (-10805 : concreteLocalField)⁻¹

theorem S2690PaperQ_eq_TateQ_iff_condition :
    S2690PaperQ = S2690TateQ → S2690PaperQ_tateJK_condition :=
  S2690PaperQ_eq_TateQ_implies_tateJK

#print axioms S2690TateQ_exists
#print axioms S2690TateQ_tateJK

end LeanFormal.IUT.XiFPaper.S2690TateQInstantiationActualAdapted
end
