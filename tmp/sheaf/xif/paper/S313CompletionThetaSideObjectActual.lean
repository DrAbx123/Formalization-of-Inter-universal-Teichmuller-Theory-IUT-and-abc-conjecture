/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.S307QPilotThetaCarrierActual
import tmp.sheaf.xif.paper.TwoLthRootQVActual
import tmp.sheaf.xif.paper.PaperFinalLValuedHaarMuLogGapActual
import tmp.sheaf.xif.paper.S312QPilotRootTensorBaseChangeActual

-- S313 reset: ThetaSideObject on the completion block qVFamTensorBlock (the
-- qPilot carrier), using the completion 2l-th root from a NatRootSystem.
-- The L/root-extension carrier is not used.  The root datum is an explicit
-- input; the exact source-root gap is recorded, not fabricated.

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S313CompletionThetaSideObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S307QPilotThetaCarrierActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedHaarMuLogGapActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev CompletionThetaCarrier : Type := qVFamTensorBlock T b

-- Completion 2l-th root of q_v transported to qVFamTensorBlock.
noncomputable def completionThetaRoot
    (R : NatRootSystem (qVUnit T b)) : CompletionThetaCarrier T b :=
  (qVFamBlockLinearEquiv T b).symm
    ((normalizedCompletionRingEquiv (qVFamTensorPlace T b)).symm
      (twoLthRoot T b R))

noncomputable def completionThetaImage
    (R : NatRootSystem (qVUnit T b)) (j : SignedLabel l.value) :
    CompletionThetaCarrier T b :=
  completionThetaRoot T b R ^ (gaussExponent j.1).toNat

noncomputable def completionThetaImageSet
    (R : NatRootSystem (qVUnit T b)) : Set (CompletionThetaCarrier T b) :=
  Set.range (completionThetaImage (l := l) T b R)

noncomputable def completionThetaReference : Set (CompletionThetaCarrier T b) :=
  Metric.closedBall (0 : CompletionThetaCarrier T b) 1

noncomputable def completionThetaScaledRegion
    (R : NatRootSystem (qVUnit T b)) (j : SignedLabel l.value) :
    Set (CompletionThetaCarrier T b) :=
  (fun x => completionThetaImage (l := l) T b R j * x) '' completionThetaReference T b

noncomputable def completionThetaHull
    (R : NatRootSystem (qVUnit T b)) : Set (CompletionThetaCarrier T b) :=
  completionThetaImageSet (l := l) T b R ∪
    ⋃ j : SignedLabel l.value, completionThetaScaledRegion (l := l) T b R j

noncomputable def completionThetaHaar : Measure (CompletionThetaCarrier T b) :=
  qVFamBlockHaar T b

noncomputable def completionThetaHullMeasure
    (R : NatRootSystem (qVUnit T b)) : ENNReal :=
  completionThetaHaar T b (completionThetaHull (l := l) T b R)

noncomputable def completionThetaHullLog
    (R : NatRootSystem (qVUnit T b)) : Real :=
  Real.log (completionThetaHullMeasure (l := l) T b R).toReal

structure CompletionThetaSideObject (R : NatRootSystem (qVUnit T b)) where
  qPilotPoint : CompletionThetaCarrier T b
  qPilotPoint_eq : qPilotPoint = qPilotBlockPoint T b
  image : Set (CompletionThetaCarrier T b)
  image_eq : image = completionThetaImageSet (l := l) T b R
  hull : Set (CompletionThetaCarrier T b)
  hull_eq : hull = completionThetaHull (l := l) T b R
  image_subset_hull : image ⊆ hull
  haar : Measure (CompletionThetaCarrier T b)
  haar_eq : haar = completionThetaHaar T b
  hullMeasure : ENNReal
  hullMeasure_eq : hullMeasure = completionThetaHullMeasure (l := l) T b R
  hullLog : Real
  hullLog_eq : hullLog = completionThetaHullLog (l := l) T b R

noncomputable def completionThetaSideObject
    (R : NatRootSystem (qVUnit T b)) : CompletionThetaSideObject T b R where
  qPilotPoint := qPilotBlockPoint T b
  qPilotPoint_eq := rfl
  image := completionThetaImageSet (l := l) T b R
  image_eq := rfl
  hull := completionThetaHull (l := l) T b R
  hull_eq := rfl
  image_subset_hull := fun x hx => Or.inl hx
  haar := completionThetaHaar T b
  haar_eq := rfl
  hullMeasure := completionThetaHullMeasure (l := l) T b R
  hullMeasure_eq := rfl
  hullLog := completionThetaHullLog (l := l) T b R
  hullLog_eq := rfl
def CompletionThetaRootSourceGap : Prop :=
  Nonempty (NatRootSystem (qVUnit T b))

#check completionThetaRoot
#check completionThetaImage
#check completionThetaHull
#check completionThetaHaar
#check completionThetaSideObject
#check CompletionThetaRootSourceGap

end LeanFormal.IUT.XiFPaper.S313CompletionThetaSideObjectActual

end