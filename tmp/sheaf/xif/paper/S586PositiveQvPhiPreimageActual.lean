import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

/-! # S586: positive QvPhi preimage from S575 positiveUnit, conditional on the divisor eval lemma -/

namespace LeanFormal.IUT.XiFPaper.S586PositiveQvPhiPreimageActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

/-- Exact missing divisor-evaluation datum for the positive unit. -/
structure PositiveQvPhiPreimageEvalData (qOrder : ℕ) where
  qOrder_pos : 0 < qOrder
  eval_eq :
    (s566Input (K := K) P).divisor A.base
      (Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))) =
      Algebra.GrothendieckAddGroup.of
        (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier)

/-- Actual positive qOrder preimage under the explicit eval lemma:
`rationalFunction = ULift.up (positiveUnit)`, `divisor = ULift.up qOrder`. -/
noncomputable def positiveQvPhiPreimageS586
    (qOrder : ℕ) (hEval : PositiveQvPhiPreimageEvalData (K := K) P A qOrder) :
    PositiveQvPhiPreimage (K := K) P A qOrder where
  qOrder_pos := hEval.qOrder_pos
  rationalFunction :=
    Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))
  divisor :=
    (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier)
  divisor_eq := hEval.eval_eq

theorem positiveQvPhiPreimageS586_rationalFunction
    (qOrder : ℕ) (hEval : PositiveQvPhiPreimageEvalData (K := K) P A qOrder) :
    (positiveQvPhiPreimageS586 (K := K) P A qOrder hEval).rationalFunction =
      Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder)) := rfl

theorem positiveQvPhiPreimageS586_divisor
    (qOrder : ℕ)
    (hEval : PositiveQvPhiPreimageEvalData (K := K) P A qOrder) :
    (positiveQvPhiPreimageS586 (K := K) P A qOrder hEval).divisor =
      (ULift.up qOrder : ((qvPhi (K := K) P.ramification).obj A.base).carrier) := rfl

/-- The eval lemma is exactly the remaining gap. -/
def PositiveQvPhiPreimageEvalRequired (qOrder : ℕ) : Prop :=
  Nonempty (PositiveQvPhiPreimageEvalData (K := K) P A qOrder)

theorem positiveQvPhiPreimage_of_eval
    (qOrder : ℕ)
    (hEval : PositiveQvPhiPreimageEvalData (K := K) P A qOrder) :
    Nonempty (PositiveQvPhiPreimage (K := K) P A qOrder) :=
  ⟨positiveQvPhiPreimageS586 (K := K) P A qOrder hEval⟩

end LeanFormal.IUT.XiFPaper.S586PositiveQvPhiPreimageActual

end
