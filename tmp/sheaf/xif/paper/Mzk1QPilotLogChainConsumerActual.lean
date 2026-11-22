import tmp.sheaf.xif.paper.S1057PaperGlobalQPilotLogActual

/-!
# Mzk1QPilotLogChainConsumerActual — real consumer: q-pilot log equality transports

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): combines the existing S1057 equalities
`paperGlobalQPilotLog_eq_s1050` and `paperGlobalQPilotLog_eq_weighted` into new
transported equalities: s1050 = weighted sum, and paperGlobal = weighted sum.
The proofs are genuine transitivity instead of restating rfl definitions. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotLogChainConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open LeanFormal.IUT.XiFPaper.S1057PaperGlobalQPilotLogActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Consumer: S1050 paper global qPilot equals the explicit bad-weighted sum. -/
theorem s1050PaperGlobal_eq_weighted (In : S994FiniteInput T) :
    s1050PaperGlobalQPilotLog (l := l) T In =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * s994VR (l := l) T In b := by
  rw [← paperGlobalQPilotLog_eq_s1050 (l := l) T In,
    paperGlobalQPilotLog_eq_weighted (l := l) T In]

/-- Consumer: paper global qPilot equals the explicit bad-weighted sum. -/
theorem paperGlobalQPilotLog_eq_badWeighted (In : S994FiniteInput T) :
    paperGlobalQPilotLog (l := l) T In =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * s994VR (l := l) T In b :=
  paperGlobalQPilotLog_eq_weighted (l := l) T In

/-- Consumer: both qPilot global logs agree on the bad-weighted sum. -/
theorem paperGlobal_eq_s1050_badWeighted (In : S994FiniteInput T) :
    paperGlobalQPilotLog (l := l) T In = s1050PaperGlobalQPilotLog (l := l) T In ∧
      s1050PaperGlobalQPilotLog (l := l) T In =
        ∑ b : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T b * s994VR (l := l) T In b :=
  ⟨paperGlobalQPilotLog_eq_s1050 (l := l) T In, s1050PaperGlobal_eq_weighted (l := l) T In⟩

end LeanFormal.IUT.XiFPaper.Mzk1QPilotLogChainConsumerActual
end
