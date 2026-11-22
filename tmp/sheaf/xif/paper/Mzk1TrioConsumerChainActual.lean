import tmp.sheaf.xif.paper.Mzk1AbsoluteKummerTrioActual

/-!
# Mzk1TrioConsumerChainActual — consumer theorems for the absolute Kummer trio bundle
(Mzk1AbsoluteKummerTrioActual, EXIT0). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TrioConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1AbsoluteKummerTrioActual

/-- Consumer: the absolute Kummer trio bundle is nonempty. -/
theorem consumer_trio_nonempty (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) :
    Nonempty (AbsoluteKummerTrio K n hμ) :=
  absoluteKummerTrio_nonempty K n hμ

/-- Consumer: the trio's Kummer map has the expected codomain (projection). -/
theorem consumer_trio_kummerMap_apply (K : Type*) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n)) (a : Kˣ) :
    (absoluteKummerTrio K n hμ).kummerMap a =
      AbsoluteKummerInjection.absoluteKummerMap hμ a := rfl

/-- Consumer: the trio row record has six rows. -/
theorem consumer_trio_rows_length : absoluteKummerTrioRows.length = 6 :=
  absoluteKummerTrioRows_length

/-- Consumer: theta-to-elliptic surjectivity (tree EtaleThetaQuotient). -/
theorem consumer_thetaToElliptic_surjective (G : Type) [Group G] :
    Function.Surjective (thetaToElliptic G) :=
  thetaToElliptic_surjective G

#check consumer_trio_nonempty
#check consumer_trio_kummerMap_apply
#check consumer_trio_rows_length
#check consumer_thetaToElliptic_surjective

end LeanFormal.IUT.XiFPaper.Mzk1TrioConsumerChainActual
end
