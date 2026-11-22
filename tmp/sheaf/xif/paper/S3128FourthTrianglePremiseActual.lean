import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
namespace LeanFormal.IUT.XiFPaper.S3128FourthTrianglePremiseActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Stage 1 fourth-triangle premise packaged from the actual comparison API:
paper-direction comparison plus nonnegative q-pilot magnitude. -/
def S3128Stage1FourthTrianglePremise
    (h : GlobalComparisonCondition (I := I) R n) : Prop :=
  qPilotThetaHullComparison (I := I) R n ∧
    0 <= qPilotMagnitude (I := I)

theorem S3128Stage1FourthTrianglePremise_holds
    (h : GlobalComparisonCondition (I := I) R n) :
    S3128Stage1FourthTrianglePremise (I := I) R n h :=
  ⟨qPilotThetaHullComparison_of_condition (I := I) R n h,
    qPilotMagnitude_nonneg (I := I)⟩

/-- Consumer: the actual comparison data (no inequality asserted). -/
noncomputable def S3128Stage1FourthTriangleData :
    GlobalHullQPilotComparisonData (I := I) R n :=
  globalHullQPilotComparisonData (I := I) R n

theorem S3128Stage1FourthTriangle_condition_iff :
    GlobalComparisonCondition (I := I) R n ↔
      qPilotThetaHullComparison (I := I) R n :=
  GlobalComparisonCondition_iff (I := I) R n

#check S3128Stage1FourthTrianglePremise
#check S3128Stage1FourthTrianglePremise_holds
#check S3128Stage1FourthTriangleData
#check S3128Stage1FourthTriangle_condition_iff
end LeanFormal.IUT.XiFPaper.S3128FourthTrianglePremiseActual