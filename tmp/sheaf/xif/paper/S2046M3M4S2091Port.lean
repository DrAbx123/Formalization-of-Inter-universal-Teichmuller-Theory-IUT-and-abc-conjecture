import tmp.sheaf.xif.paper.S2091H2ZhatActual
import tmp.sheaf.xif.paper.S2046M4ConditionalActual

-- S2046 M3/M4 via S2091: actual H2 port and M3 limit reduction;
-- G1/G2/G3 remain exact missing, no fake.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046M3M4S2091Port

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2091H2ZhatActual
open LeanFormal.IUT.XiFPaper.S2046M4ConditionalActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The ported actual H^2 isomorphism H2ZHatOne ≃* Zhat. -/
noncomputable abbrev S2046H2ZHatEquiv :
    Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Zhat :=
  h2ZHatOneEquiv_of_port p

/-- The ported Br(Q_p) ≃ Q/Z. -/
noncomputable abbrev S2046BrEquivQZ :
    Brauer.Br ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Brauer.QZ :=
  brEquivQZ p

/-- Exact M3 first missing: cochain-model H^2 limit comparison. -/
abbrev S2046M3LimitComparisonRequired : Prop :=
  PsiCnsH2LimitComparison p

/-- Actual M3 equivalence from the limit comparison and the port. -/
noncomputable def S2046M3EquivOfLimit
    (h : S2046M3LimitComparisonRequired p) :
    PsiCnsH2 p ≃* Multiplicative Zhat :=
  Classical.choice (PsiCnsH2Normalization_of_limitComparison p h)

theorem S2046M3Normalization_ofLimit
    (h : S2046M3LimitComparisonRequired p) :
    PsiCnsH2Normalization p :=
  PsiCnsH2Normalization_of_limitComparison p h

theorem S2046M3_iff_limitComparison :
    PsiCnsH2Normalization p ↔ S2046M3LimitComparisonRequired p :=
  PsiCnsH2Normalization_iff_limitComparison p

/-- M4 exact first missing, unchanged: normalization + Kummer image. -/
abbrev S2046M4KummerNormalizationRequired : Prop :=
  PsiCnsKummerNormalization p

/-- M4 local-units conditional port from S2046M4ConditionalActual. -/
theorem S2046M4LocalUnits_sufficient
    (h : S2046M4KummerNormalizationRequired p) :
    Nonempty (LocalOFieldUnits p ≃*
      (Submonoid.comap (kummerImage_equiv_nonnegative_of_normalization p h).choose
        zhatNatMonoid)ˣ) :=
  S2046M4_sufficient p h

#check S2046H2ZHatEquiv
#check S2046BrEquivQZ
#check S2046M3LimitComparisonRequired
#check S2046M3EquivOfLimit
#check S2046M3Normalization_ofLimit
#check S2046M3_iff_limitComparison
#check S2046M4KummerNormalizationRequired
#check S2046M4LocalUnits_sufficient

#print axioms S2046H2ZHatEquiv
#print axioms S2046BrEquivQZ
#print axioms S2046M3EquivOfLimit
#print axioms S2046M3Normalization_ofLimit
#print axioms S2046M3_iff_limitComparison
#print axioms S2046M4LocalUnits_sufficient

end LeanFormal.IUT.XiFPaper.S2046M3M4S2091Port

end