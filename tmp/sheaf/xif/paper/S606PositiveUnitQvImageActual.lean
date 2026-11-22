import tmp.sheaf.xif.paper.S598QvPhiQOrderTauFromQvOrderActual
import tmp.sheaf.xif.paper.S591PositiveUnitDivisorEvalActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S606PositiveUnitQvImageActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S598QvPhiQOrderTauFromQvOrderActual
open Iut.SourceModelFrobenioid
open Iut.SourceFinitePlaceReconstruction
open Additive

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

theorem positiveUnit_valuation_qvOrder :
    Multiplicative.toAdd ((P.valuation A.base).valuation
      (positiveUnit (K := K) P A (qVFamilyK T b).order)) =
      ((qVFamilyK T b).order : ℤ) := by
  rw [positiveUnit_valuation (K := K) P A (qVFamilyK T b).order]

theorem positiveUnit_divisor_qvOrder :
    (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up
        (positiveUnit (K := K) P A (qVFamilyK T b).order))) =
    Algebra.GrothendieckAddGroup.of
      (ULift.up (qVFamilyK T b).order :
        ((qvPhi (K := K) P.ramification).obj A.base).carrier) := by
  exact positiveUnit_divisor_eval (K := K) P A (qVFamilyK T b).order

/-- Exact missing actual image comparison: the K-side q_v unit and its image
in the cover field.  The repo has no canonical map from the completion of the
qVFamilyK place to `coverField A.base`. -/
structure QvPositiveUnitImageGap where
  qUnit : (Completion (qVFamilyKLift T b))ˣ
  qUnit_eq : qUnit =
    Units.mk0 (qVFamilyK T b).q (qVFamilyK T b).q_ne_zero
  image : (Completion (qVFamilyKLift T b))ˣ → (coverField A.base)ˣ
  image_q : image qUnit =
    positiveUnit (K := K) P A (qVFamilyK T b).order

def QvPositiveUnitImageRequired : Prop :=
  Nonempty (QvPositiveUnitImageGap (K := K) T b P A)

end LeanFormal.IUT.XiFPaper.S606PositiveUnitQvImageActual

end
