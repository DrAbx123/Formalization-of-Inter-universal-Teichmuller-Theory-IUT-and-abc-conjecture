import tmp.sheaf.xif.paper.S957TensorClosureContainmentActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual

/-! # S960: pointwise qPilot approximation by thetaImageIndUnion

qPilot region is exactly the j=1 theta region at cRoot, so its transported
image is the j=1 theta image.  Approximation of every transported qPilot
point by thetaImageIndUnion points is the S957 pointwise density property.
Region/image identities are actual; the density itself needs the topology
and the theta image base dense in the qPilot region, so it is recorded as an
exact input.  No union containment is claimed. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S960PointwiseApproxActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S957TensorClosureContainmentActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData T b)

/-- qPilot region is the j=1 theta region at cRoot. -/
theorem qPilotPaperRegion_eq_rootThetaRegion_one :
    qPilotPaperRegion (l := l) T b =
      rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b) (oneLabel l) := by
  unfold qPilotPaperRegion thetaTensorScaledRegion rootThetaRegion
  congr 1
  congr 1
  congr 1
  funext i
  rw [gaussExponent_oneLabel]
  ring

/-- Transported qPilot image equals the transported j=1 theta image. -/
theorem qPilotImage_eq_thetaJ1Image :
    qPilotPaperImageInLValued (l := l) T b =
      qVFamToLValued (l := l) T b ''
        (rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
          (paperRootCoefficientFamily (l := l) T b) (oneLabel l)) := by
  unfold qPilotPaperImageInLValued
  rw [qPilotPaperRegion_eq_rootThetaRegion_one]

/-- S957 pointwise density, transported: every qPilot image point is in the
closure of thetaImageIndUnion under the exact topology D.topologicalSpace. -/
def S960Density : Prop :=
  ∀ x : qVFamTensorBlock T b, x ∈ qPilotPaperRegion (l := l) T b →
    qVFamToLValued (l := l) T b x ∈ paperTensorHull (l := l) T b D

/-- Exact equivalence with S957 pointwise accumulation. -/
theorem s960Density_iff_s957 :
    S960Density T b D ↔
      S957ThetaAccumulatesQPilot (l := l) T b D := by
  unfold S960Density S957ThetaAccumulatesQPilot
  constructor <;> intro h <;> exact h

/-- Exact minimal input: topology/base density. -/
def S960TopologyBaseDensityRequired : Prop :=
  S960Density T b D

end LeanFormal.IUT.XiFPaper.S960PointwiseApproxActual
end
