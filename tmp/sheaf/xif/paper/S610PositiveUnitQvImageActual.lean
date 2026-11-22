import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
import tmp.sheaf.xif.paper.S546QHalfCandidateActual

/-! # S610: positiveUnit/qOrder as the q_v image — exact comparison

`positiveUnit` is chosen in the finite étale cover field `coverField A.base` by
surjectivity of the cover valuation.  `qVFamilyK` lives in the K-side
completion `Completion (qVFamilyKLift T b)`.  There is no actual map from that
completion into `coverField A.base`; `qHalfRoot`/`tateParameterUnit` live in
the algebraic closure/completion of the F-side place.  Therefore the image
equality is not typable from the current data and is recorded exactly.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S610PositiveUnitQvImageActual

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
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

/-- positiveUnit at qVFamilyK.order. -/
noncomputable def positiveUnitAtQvOrder :
    (coverField A.base)ˣ :=
  positiveUnit P A (qVFamilyK T b).order

/-- Its valuation exponent is exactly the qVFamilyK order. -/
theorem positiveUnitAtQvOrder_valuation :
    Multiplicative.toAdd
      ((P.valuation A.base).valuation (positiveUnitAtQvOrder T b P A)) =
      ((qVFamilyK T b).order : ℤ) :=
  positiveUnit_valuation P A (qVFamilyK T b).order

/-- Exact missing image comparison between the completion q_v unit and the
cover-field positiveUnit. -/
structure PositiveUnitQvImageData where
  qv : (Completion (qVFamilyKLift T b))ˣ
  image : (coverField A.base)ˣ
  image_eq : Prop
  valuation_eq : Prop

def PositiveUnitQvImageDataRequired : Prop :=
  Nonempty (PositiveUnitQvImageData (K := K) T b P A)

end LeanFormal.IUT.XiFPaper.S610PositiveUnitQvImageActual
end
