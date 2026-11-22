import tmp.sheaf.xif.paper.S610PositiveUnitQvImageActual
import tmp.sheaf.xif.paper.S606PositiveUnitQvImageActual
/-! # S612: element-level qUnit -> positiveUnit image map
The qUnit lives in the K-side completion; positiveUnit lives in the finite
etale cover field.  There is no canonical completion-to-cover map in the tree.
This file constructs the actual qUnit/positiveUnit elements and records the
element-level map plus its qUnit image equality as the exact missing datum. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S612QvPositiveUnitImageMapActual
open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S606PositiveUnitQvImageActual
open LeanFormal.IUT.XiFPaper.S610PositiveUnitQvImageActual
open Iut.SourceModelFrobenioid
universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))
/-- Actual qUnit in the K-side completion. -/
noncomputable def qUnitAtQvFamilyK : (Completion (qVFamilyKLift T b))ˣ :=
  Units.mk0 (qVFamilyK T b).q (qVFamilyK T b).q_ne_zero
theorem qUnitAtQvFamilyK_val :
    (qUnitAtQvFamilyK T b : Completion (qVFamilyKLift T b)) =
      (qVFamilyK T b).q := rfl
/-- Actual positiveUnit in the cover field. -/
noncomputable def positiveUnitAtQvOrder' : (coverField A.base)ˣ :=
  positiveUnit (K := K) P A (qVFamilyK T b).order
/-- Element-level map from completion units to cover-field units, with the
qUnit image equality.  This is the exact missing map datum. -/
structure QvPositiveUnitElementMap where
  toFun : (Completion (qVFamilyKLift T b))ˣ → (coverField A.base)ˣ
  map_qUnit : toFun (qUnitAtQvFamilyK T b) =
    positiveUnitAtQvOrder' (K := K) T b P A
def QvPositiveUnitElementMapRequired : Prop :=
  Nonempty (QvPositiveUnitElementMap (K := K) T b P A)
/-- S606 gap is exactly the element-level map plus qUnit equality. -/
def QvPositiveUnitImageGapViaMap : Prop :=
  QvPositiveUnitImageRequired (K := K) T b P A
end LeanFormal.IUT.XiFPaper.S612QvPositiveUnitImageMapActual
