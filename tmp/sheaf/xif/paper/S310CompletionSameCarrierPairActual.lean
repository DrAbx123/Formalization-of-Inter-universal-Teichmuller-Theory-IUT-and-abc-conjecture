/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.S22DependentProductActual
import tmp.sheaf.xif.paper.TwoLthRootQVActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

/-!
# S310: same-carrier completion pair for qPilot and Theta

This reset uses the completion block carrier

  DependentCompletionProduct T = (b : Bad) -> Completion((nativeBadLift T).lift b)

directly.  The qPilot image point is the actual qVFamily product point.  Theta
image points are built from the completion 2l-th root q_v^(1/2l), conditional
on the actual completion root data of TwoLthRootQVActual.

The completion root system is not constructed in the tree; its existence is
recorded exactly.  The Theta paper hull on this completion carrier is also not
constructed; that object is recorded as an exact hull gap.  No L-valued,
double-count, Dirac, or fake hull object is used.  No inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S310CompletionSameCarrierPairActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual completion root data family for all bad places. -/
abbrev CompletionRootDataFamily : Type :=
  (b : Bad (nativePlaceSelection T)) -> TwoLthRootData T b

/-- Exact missing completion root-system existence. -/
def CompletionRootSystemExistenceGap : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    Nonempty (NatRootSystem (qVUnit T b))

/-- The exact root-existence gap is the S212 root gap, pointwise. -/
theorem CompletionRootSystemExistenceGap_iff :
    CompletionRootSystemExistenceGap T ↔
      ∀ b : Bad (nativePlaceSelection T), TwoLRootExistenceGap T b :=
  Iff.rfl

/-- qPilot image point in the completion carrier: the actual qVFamily product
point. -/
noncomputable def qPilotCompletionImagePoint : DependentCompletionProduct T :=
  dependentQVFamProductPoint T

/-- Theta image point at label j from actual completion root data: root_b^(j^2). -/
noncomputable def thetaCompletionImagePoint
    (R : CompletionRootDataFamily T)
    (j : SignedLabel l.value) : DependentCompletionProduct T :=
  fun b => ((R b).root : Completion ((nativeBadLift T).lift b)) ^
    (gaussExponent j.1).toNat

/-- Theta completion image set from root data. -/
noncomputable def thetaCompletionImageSet
    (R : CompletionRootDataFamily T) :
    Set (DependentCompletionProduct T) :=
  Set.range (fun j : SignedLabel l.value =>
    thetaCompletionImagePoint T R j)

/-- Exact completion-carrier Theta hull object.  Its hull is actual data; the
tree does not construct it from the root image. -/
structure ThetaCompletionHullGap
    (R : CompletionRootDataFamily T) where
  hull : Set (DependentCompletionProduct T)
  image_subset : thetaCompletionImageSet T R ⊆ hull
  paper_hull_condition : Prop
  haar_condition : Prop

/-- Exact missing paper Theta hull on the completion carrier. -/
def ThetaCompletionHullGapRequired
    (R : CompletionRootDataFamily T) : Prop :=
  Nonempty (ThetaCompletionHullGap T R)

/-- Same-carrier completion pair, conditional on root data and the exact Theta
hull object.  Both sides are sets/points of DependentCompletionProduct T. -/
structure CompletionSameCarrierPair
    (R : CompletionRootDataFamily T)
    (H : ThetaCompletionHullGap T R) where
  qPilotImagePoint : DependentCompletionProduct T
  qPilotImagePoint_eq : qPilotImagePoint = qPilotCompletionImagePoint T
  thetaImageSet : Set (DependentCompletionProduct T)
  thetaImageSet_eq : thetaImageSet = thetaCompletionImageSet T R
  thetaHull : Set (DependentCompletionProduct T)
  thetaHull_eq : thetaHull = H.hull
  thetaImage_subset_hull : thetaImageSet ⊆ thetaHull

/-- Conditional actual same-carrier completion pair. -/
noncomputable def completionSameCarrierPair
    (R : CompletionRootDataFamily T)
    (H : ThetaCompletionHullGap T R) :
    CompletionSameCarrierPair T R H where
  qPilotImagePoint := qPilotCompletionImagePoint T
  qPilotImagePoint_eq := rfl
  thetaImageSet := thetaCompletionImageSet T R
  thetaImageSet_eq := rfl
  thetaHull := H.hull
  thetaHull_eq := rfl
  thetaImage_subset_hull := H.image_subset

/-- Exact simultaneous gap: some completion root data family together with
its Theta hull object. -/
def CompletionRootAndThetaHullGap : Prop :=
  ∃ R : CompletionRootDataFamily T,
    Nonempty (ThetaCompletionHullGap T R)

/-- The same-carrier completion pair exists exactly when a root data family and
its Theta hull object exist. -/
theorem completionSameCarrierPair_iff_gap :
    Nonempty (Sigma (fun R : CompletionRootDataFamily T =>
      ThetaCompletionHullGap T R)) ↔
      CompletionRootAndThetaHullGap T := by
  constructor
  · rintro ⟨⟨R, H⟩⟩
    exact ⟨R, ⟨H⟩⟩
  · rintro ⟨R, hH⟩
    exact ⟨⟨R, Classical.choice hH⟩⟩

end LeanFormal.IUT.XiFPaper.S310CompletionSameCarrierPairActual

end
