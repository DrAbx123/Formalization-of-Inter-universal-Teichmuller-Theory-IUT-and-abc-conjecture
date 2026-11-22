import tmp.sheaf.xif.paper.Mzk1EtThRow6RealizationActual
import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual

/-!
# Mzk1Row6ConsumerChainActual — consumer theorems for the EtTh row-6 carrier package
(Mzk1EtThRow6RealizationActual + IKT, EXIT0). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Row6ConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1EtThRow6RealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual

/-- Consumer: the row-6 carrier package is nonempty for every datum. -/
theorem consumer_row6_nonempty (l : PrimeGeFive) (K : Type*) [Field K] [CharZero K]
    (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type*) [Group G] : Nonempty (EtThRow6RealizationCarrier l K n hμ G) :=
  etThRow6RealizationCarrier_nonempty l K n hμ G

/-- Consumer: the row-6 carrier's theta-to-elliptic map is surjective. -/
theorem consumer_row6_theta_surjective (l : PrimeGeFive) (K : Type*) [Field K] [CharZero K]
    (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type*) [Group G] :
    Function.Surjective (etThRow6RealizationCarrier l K n hμ G).thetaToElliptic :=
  (etThRow6RealizationCarrier l K n hμ G).thetaToElliptic_surjective

/-- Consumer: the row-6 carrier's Kummer quotient is injective. -/
theorem consumer_row6_quotient_injective (l : PrimeGeFive) (K : Type*) [Field K] [CharZero K]
    (n : ℕ) [NeZero n]
    (hμ : AbsoluteKummerInjection.RootsOfUnityFixed (K := K) (n := n))
    (G : Type*) [Group G] :
    Function.Injective (etThRow6RealizationCarrier l K n hμ G).quotientInjective :=
  (etThRow6RealizationCarrier l K n hμ G).quotientInjective

/-- Consumer: the row-6 status record has five rows. -/
theorem consumer_row6_rows_length : etThRow6Rows.length = 5 :=
  etThRow6Rows_length

#check consumer_row6_nonempty
#check consumer_row6_theta_surjective
#check consumer_row6_quotient_injective
#check consumer_row6_rows_length

end LeanFormal.IUT.XiFPaper.Mzk1Row6ConsumerChainActual
end
