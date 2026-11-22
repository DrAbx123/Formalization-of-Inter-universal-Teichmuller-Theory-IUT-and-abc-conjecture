import tmp.sheaf.xif.paper.S2570TateIntegralModelActual
import tmp.sheaf.xif.paper.S2572TateDeltaNormActual
import Mathlib.RingTheory.LocalRing.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2568TateCoefficientNormActual
open LeanFormal.IUT.XiFPaper.S2569TateA6UnconditionalActual
open LeanFormal.IUT.XiFPaper.S2570TateIntegralModelActual
open LeanFormal.IUT.XiFPaper.S2572TateDeltaNormActual

namespace LeanFormal.IUT.XiFPaper.S2573TateMinimalActual

variable {K : Type*} [Field K] [NumberField K]
variable (p : NumberField.FinitePlace K) (q : Completion p) (hq : ‖q‖ < 1)

abbrev WK : WeierstrassCurve (Completion p) := TateCurve.weierstrassCurve (Completion p) q
abbrev Wint : WeierstrassCurve (CompletionIntegers p) := S2570TateIntegralModel p q hq

theorem S2573_a4_norm_lt_one (hq : ‖q‖ < 1) : ‖((Wint p q hq).a₄ : Completion p)‖ < 1 := by
  change ‖TateCurve.a4 (Completion p) q‖ < 1
  exact lt_of_le_of_lt (S2568_norm_a4_le (K := Completion p) hq) hq

theorem S2573_a6_norm_lt_one (hq : ‖q‖ < 1) : ‖((Wint p q hq).a₆ : Completion p)‖ < 1 := by
  change ‖TateCurve.a6 (Completion p) q‖ < 1
  exact lt_of_le_of_lt (S2569_norm_a6_le_unconditional (K := Completion p) q hq) hq

theorem S2573_WK_delta_norm_lt_one (hq : ‖q‖ < 1) : ‖(WK p q).Δ‖ < 1 := by
  have h4 := S2573_a4_norm_lt_one p q hq
  have h6 := S2573_a6_norm_lt_one p q hq
  have h := S2572_delta_norm_lt_one (K := Completion p) h4 h6
  have hmk : WeierstrassCurve.mk 1 0 0 ((Wint p q hq).a₄ : Completion p)
      ((Wint p q hq).a₆ : Completion p) = WK p q := by
    rw [show WK p q = (Wint p q hq).map (CompletionIntegers p).subtype from
      (S2570TateIntegralModel_map p q hq).symm]
    ext <;> simp [Wint, S2570TateIntegralModel]
  simpa [hmk] using h

theorem S2573_Wint_c4_isUnit (hq : ‖q‖ < 1) : IsUnit (Wint p q hq).c₄ := by
  have hc4 : (Wint p q hq).c₄ = 1 - 48 * (Wint p q hq).a₄ := by
    simp [Wint, S2570TateIntegralModel, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  rw [hc4]
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  exact (IsLocalRing.mem_maximalIdeal _).mp (by
    rw [IsLocalRing.mem_maximalIdeal]
    exact Ideal.mul_mem_left _ (48 : CompletionIntegers p)
      (S2570_a4_mem_maximalIdeal p q hq))

#check S2573_WK_delta_norm_lt_one
#check S2573_Wint_c4_isUnit
#print axioms S2573_WK_delta_norm_lt_one
#print axioms S2573_Wint_c4_isUnit
end LeanFormal.IUT.XiFPaper.S2573TateMinimalActual
end