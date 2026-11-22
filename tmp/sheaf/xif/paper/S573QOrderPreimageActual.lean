import tmp.sheaf.xif.paper.S567QvPhiQOrderFieldsFromTriDataActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S573QOrderPreimageActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S553QvPhiTriDataActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S567QvPhiQOrderFieldsFromTriDataActual
open Iut.SourceModelFrobenioid
universe u
variable {K : Type u} [Field K]
variable (T : QvPhiTriData (K := K))
variable (D : S556InputDataActual (K := K))
variable (A : Object (qvPhi (K := K) D.ramification))
/-- From an explicit unit and the aligned-divisor formula, build the S567
qOrder preimage. -/
noncomputable def s567QOrderPreimageOfUnit
    (u : (coverField A.base)ˣ)
    (hformula : (s567Input (K := K) D).divisor A.base
      (Additive.ofMul (ULift.up u)) =
        Algebra.GrothendieckAddGroup.of
          (ULift.up (T.qOrder A.base) :
            ((qvPhi (K := K) D.ramification).obj A.base).carrier)) :
    S567QOrderPreimage (K := K) T D A where
  divisor := ULift.up (T.qOrder A.base)
  divisor_eq := rfl
  rationalFunction := Additive.ofMul (ULift.up u)
  divisor_eq' := hformula
/-- Exact missing unit/formula data for the positive qOrder preimage. -/
structure S573QOrderPreimageUnitData where
  unit : (coverField A.base)ˣ
  formula : (s567Input (K := K) D).divisor A.base
    (Additive.ofMul (ULift.up unit)) =
      Algebra.GrothendieckAddGroup.of
        (ULift.up (T.qOrder A.base) :
          ((qvPhi (K := K) D.ramification).obj A.base).carrier)
/-- Exact missing unit/formula datum. -/
def S573QOrderPreimageRequired : Prop :=
  Nonempty (S573QOrderPreimageUnitData (K := K) T D A)
/-- The S567 exact preimage datum is equivalent to the unit/formula datum
once the unit is installed as a rational function. -/
def S573QOrderPreimageViaS567 : Prop :=
  S567QOrderPreimageRequired (K := K) T D A
end LeanFormal.IUT.XiFPaper.S573QOrderPreimageActual
