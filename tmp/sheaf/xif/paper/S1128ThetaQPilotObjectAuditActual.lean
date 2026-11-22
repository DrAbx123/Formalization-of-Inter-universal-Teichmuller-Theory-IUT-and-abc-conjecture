import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.GlobalQPilotObjectActual
import tmp.sheaf.xif.paper.QVFamRootThetaTensorLiftActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

-- S1128: audit of actual/Thetas q-pilot objects.
-- PaperQPilotObjectSourceActual is read/reported but cannot be co-imported:
-- its import tmp.sheaf.xif.PaperQPilotObject conflicts with the paper/
-- PaperQPilotObject used by GlobalQPilotObjectActual (duplicate declarations).
-- Reports actual constructions and exact gaps; does NOT assert any
-- inhabited paper object or any missing identification.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1128ThetaQPilotObjectAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source.GlobalQPilotObjectActual
open LeanFormal.IUT.XiFPaper.QVFamRootThetaTensorLiftActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe ua uv upi umon ui uC3 uD3 uM uP u

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- (1) q-side actual: the q-pilot scalar is negative localSignedLog q. -/
theorem s1128QPilotScalar_neg
    (L : QPilotLineActual (I := I)) :
    L.qScalar < 0 :=
  L.qScalar_neg

theorem s1128QPilotLogVolume_eq_log_norm
    (L : QPilotLineActual (I := I)) :
    L.qPilotLogVolume = (Real.log ‖L.C3.q.q‖ : WithTop Real) :=
  L.qPilotLogVolume_eq_log_norm

/-- q-pilot region is the rank-one tensor unit, NOT a theta-label-1 point. -/
theorem s1128QPilotRegion_singleton
    (L : QPilotLineActual (I := I)) :
    L.qPilotRegion =
      {(L.C3.tensorUnit : ArithmeticTensorTupleBlock
        L.C3.tensorPlaces L.C3.tensorTuple)} :=
  L.qPilotRegion_eq_unit

/-- (2) paper q-pilot actual layer: magnitude positivity from actual q. -/
theorem s1128PaperQPilotMagnitude_pos
    (P : PaperQPilotObjectActual (I := I)) :
    0 < P.qPilotLogMagnitude :=
  P.qPilotLogMagnitude_pos

/-- Exact: the paper q-pilot object is a structure, not asserted inhabited. -/
def S1128PaperQPilotObjectRequired : Prop :=
  Nonempty (PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))

/-- (3) global q_v-family actual: signed log is -sum_b |log q_b|. -/
theorem s1128GlobalQPilot_eq_source
    (I : OriginalInput l V) :
    globalQPilotSignedLog I = sourceQPilotSignedLog I.initial :=
  globalQPilotSignedLog_eq_sourceQPilotSignedLog I

theorem s1128GlobalCollection_signedLogVolume
    (I : OriginalInput l V) :
    (globalQPilotCollection I).signedLogVolume =
      sourceQPilotSignedLog I.initial :=
  globalQPilotCollection_signedLogVolume I

-- (4) Theta-side actual L-valued pure-tensor lift at positive labels.
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (j : ThetaLabel (l := l))

theorem s1128ThetaTensorLift_mem_image :
    qVFamRootThetaTensorLift (l := l) T b j ∈
      qVFamRootThetaTensorImageSet (l := l) T b :=
  qVFamRootThetaTensorLift_mem_image T b j

/-- Exact Theta-side gap: the mu_{2l} action on the L-valued tensor lift. -/
def S1128ThetaMuTensorLiftRequired : Prop :=
  QVFamRootThetaMuTensorLiftGapRequired (l := l) T b

/-- (5) corrected 2l-root coefficient: old q coefficient is 2l times root. -/
theorem s1128TensorCoefficient_eq_twoL_mul_root :
    qVFamTensorCoefficient (l := l) T b =
      (2 * (l.value : Real)) * qVFamPaperRootCoefficient (l := l) T b :=
  qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient (l := l) T b

/-- Exact integrality needed for the corrected 2l-root valuation. -/
def S1128RootIntegralityRequired : Prop :=
  qVFamRootOrderIntegral (l := l) T b

/-- Summary of actual layer versus exact gaps. -/
structure S1128AuditSummary where
  qSideActual : Prop
  qSideExact : Prop
  qSideActual_eq : qSideActual = True
  qSideExact_eq : qSideExact = S1128PaperQPilotObjectRequired (I := I)
  thetaSideActual : Prop
  thetaSideActual_eq : thetaSideActual = True
  thetaSideExact : Prop
  thetaSideExact_eq : thetaSideExact = S1128ThetaMuTensorLiftRequired (l := l) T b

#check s1128QPilotScalar_neg
#check s1128QPilotRegion_singleton
#check s1128GlobalQPilot_eq_source
#check s1128ThetaTensorLift_mem_image
#check s1128TensorCoefficient_eq_twoL_mul_root
#check S1128PaperQPilotObjectRequired
#check S1128ThetaMuTensorLiftRequired
#check S1128RootIntegralityRequired

end LeanFormal.IUT.XiFPaper.S1128ThetaQPilotObjectAuditActual

end