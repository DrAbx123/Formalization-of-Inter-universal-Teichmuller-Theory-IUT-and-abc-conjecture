import tmp.sheaf.xif.paper.S2575TateMultiplicativeActual
import tmp.sheaf.xif.paper.S2574TateMinimalFinalActual
import Mathlib.RingTheory.DedekindDomain.AdicValuation

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2570TateIntegralModelActual
open LeanFormal.IUT.XiFPaper.S2573TateMinimalActual
open LeanFormal.IUT.XiFPaper.S2574TateMinimalFinalActual

namespace LeanFormal.IUT.XiFPaper.S2577TateBadReductionActual

variable {K : Type*} [Field K] [NumberField K]
variable (p : NumberField.FinitePlace K) (q : Completion p) (hq : ‖q‖ < 1)

abbrev R (p : NumberField.FinitePlace K) : Type _ := CompletionIntegers p
abbrev W (p : NumberField.FinitePlace K) (q : Completion p) : WeierstrassCurve (Completion p) :=
  TateCurve.weierstrassCurve (Completion p) q

theorem S2577_delta_mem_completionIntegers (hq : ‖q‖ < 1) :
    (W p q).Δ ∈ CompletionIntegers p := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valued.toNormedField.norm_le_one_iff).mp
    (S2573_WK_delta_norm_lt_one p q hq).le

theorem S2577_delta_mem_maximalIdeal (hq : ‖q‖ < 1) :
    (⟨(W p q).Δ, S2577_delta_mem_completionIntegers p q hq⟩ : CompletionIntegers p) ∈
      IsLocalRing.maximalIdeal (CompletionIntegers p) := by
  let y : (Valued.v : Valuation (Completion p) (WithZero (Multiplicative Int))).valuationSubring :=
    ⟨(W p q).Δ, by
      rw [Valuation.mem_valuationSubring_iff]
      exact (Valued.toNormedField.norm_le_one_iff).mp
        (S2573_WK_delta_norm_lt_one p q hq).le⟩
  change y ∈ IsLocalRing.maximalIdeal
    ((Valued.v : Valuation (Completion p) (WithZero (Multiplicative Int))).valuationSubring)
  rw [Valuation.mem_maximalIdeal_iff]
  exact (Valued.toNormedField.norm_lt_one_iff).mp
    (S2573_WK_delta_norm_lt_one p q hq)

theorem S2577_badReduction (hq : ‖q‖ < 1) :
    (IsDiscreteValuationRing.maximalIdeal (R p)).valuation (Completion p) (W p q).Δ < 1 := by
  let x : R p := ⟨(W p q).Δ, S2577_delta_mem_completionIntegers p q hq⟩
  have hx : x ∈ (IsDiscreteValuationRing.maximalIdeal (R p)).asIdeal := by
    change (⟨(W p q).Δ, S2577_delta_mem_completionIntegers p q hq⟩ : R p) ∈
      IsLocalRing.maximalIdeal (R p)
    exact S2577_delta_mem_maximalIdeal p q hq
  change (IsDiscreteValuationRing.maximalIdeal (R p)).valuation (Completion p)
    (algebraMap (R p) (Completion p) x) < 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hx

#check S2577_badReduction
#print axioms S2577_badReduction
end LeanFormal.IUT.XiFPaper.S2577TateBadReductionActual
end