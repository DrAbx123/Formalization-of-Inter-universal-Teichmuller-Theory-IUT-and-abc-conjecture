import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerQuotient
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerContinuity

/-!
# Mzk1AbsoluteKummerQuotientConsumerActual — consumer theorems over the absolute Kummer
quotient/continuity assets (OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerQuotientConsumerActual

open LeanFormal.IUT

/-- Consumer: the quotient Kummer map is injective. -/
theorem consumer_quotient_injective {K : Type} [Field K] [CharZero K] {n : ℕ} [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    Function.Injective (AbsoluteKummerQuotient.absoluteKummerMapQuotient hμ) :=
  AbsoluteKummerQuotient.absoluteKummerMapQuotient_injective hμ

/-- Consumer: continuity of the absolute Kummer class in the Galois variable
(tree re-export, discrete topology). -/
theorem consumer_continuous :=
  @AbsoluteKummerContinuity.continuous_absoluteKummerMap

#check consumer_quotient_injective
#check consumer_continuous

end LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerQuotientConsumerActual
end
