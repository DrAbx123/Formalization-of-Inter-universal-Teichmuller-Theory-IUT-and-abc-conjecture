import tmp.sheaf.xif.paper.S2575TateMultiplicativeActual
import tmp.sheaf.xif.paper.S2574TateMinimalFinalActual
import Mathlib.RingTheory.DedekindDomain.AdicValuation

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2570TateIntegralModelActual
open LeanFormal.IUT.XiFPaper.S2573TateMinimalActual
open LeanFormal.IUT.XiFPaper.S2574TateMinimalFinalActual

namespace LeanFormal.IUT.XiFPaper.S2576TateBadReductionActual

variable {K : Type*} [Field K] [NumberField K]
variable (p : NumberField.FinitePlace K) (q : Completion p) (hq : ‖q‖ < 1)

abbrev R (p : NumberField.FinitePlace K) : Type _ := CompletionIntegers p
abbrev W (p : NumberField.FinitePlace K) (q : Completion p) : WeierstrassCurve (Completion p) :=
  TateCurve.weierstrassCurve (Completion p) q

theorem S2576_badReduction :
    (IsDiscreteValuationRing.maximalIdeal (R p)).valuation (Completion p) (W p q).Δ < 1 := by
  change (underlyingPrime p).valuation (Completion p) (W p q).Δ < 1
  rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (K := K) (v := underlyingPrime p) (k := (W p q).Δ)]
  exact (Valued.toNormedField.norm_lt_one_iff).mp (S2573_WK_delta_norm_lt_one p q hq)

theorem S2576_hasMultiplicativeReduction :
    (W p q).HasMultiplicativeReduction (R p) := by
  letI : (W p q).IsMinimal (R p) := S2574_isMinimal p q hq
  exact { badReduction := S2576_badReduction p q hq,
    multiplicativeReduction := S2574_c4_valuation_eq_one p q hq }

#check S2576_badReduction
#check S2576_hasMultiplicativeReduction
#print axioms S2576_hasMultiplicativeReduction
end LeanFormal.IUT.XiFPaper.S2576TateBadReductionActual
end