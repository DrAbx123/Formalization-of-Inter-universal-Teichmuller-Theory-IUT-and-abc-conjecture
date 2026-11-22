import tmp.sheaf.xif.paper.S2573TateMinimalActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2570TateIntegralModelActual
open LeanFormal.IUT.XiFPaper.S2573TateMinimalActual

namespace LeanFormal.IUT.XiFPaper.S2574TateMinimalFinalActual

variable {K : Type*} [Field K] [NumberField K]
variable (p : NumberField.FinitePlace K) (q : Completion p) (hq : ‖q‖ < 1)

abbrev R (p : NumberField.FinitePlace K) : Type _ := CompletionIntegers p
abbrev W : WeierstrassCurve (Completion p) := TateCurve.weierstrassCurve (Completion p) q

theorem S2574_c4_eq_algebraMap (hq : ‖q‖ < 1) :
    (W p q).c₄ = algebraMap (R p) (Completion p) (Wint p q hq).c₄ := by
  have hm := S2570TateIntegralModel_map p q hq
  change (TateCurve.weierstrassCurve (Completion p) q).c₄ =
    (algebraMap (R p) (Completion p)) (Wint p q hq).c₄
  rw [← hm, WeierstrassCurve.map_c₄]
  rfl

theorem S2574_c4_valuation_eq_one (hq : ‖q‖ < 1) :
    (IsDiscreteValuationRing.maximalIdeal (R p)).valuation (Completion p) (W p q).c₄ = 1 := by
  rw [S2574_c4_eq_algebraMap p q hq]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact IsLocalRing.notMem_maximalIdeal.mpr (S2573_Wint_c4_isUnit p q hq)

theorem S2574_isIntegral (hq : ‖q‖ < 1) : (W p q).IsIntegral (R p) :=
  ⟨Wint p q hq, by
    show W p q = (Wint p q hq).map (algebraMap (R p) (Completion p))
    have hsub : (CompletionIntegers p).subtype =
        (algebraMap (R p) (Completion p)) := rfl
    have hm := S2570TateIntegralModel_map p q hq
    rw [hsub] at hm
    exact hm.symm⟩

theorem S2574_isMinimal (hq : ‖q‖ < 1) : (W p q).IsMinimal (R p) :=
  letI : (W p q).IsIntegral (R p) := S2574_isIntegral p q hq
  isMinimal_of_isIntegral_valuation_c₄_eq_one (R p) (W p q)
    (S2574_c4_valuation_eq_one p q hq)

#check S2574_c4_valuation_eq_one
#check S2574_isIntegral
#check S2574_isMinimal
#print axioms S2574_isMinimal
end LeanFormal.IUT.XiFPaper.S2574TateMinimalFinalActual
end