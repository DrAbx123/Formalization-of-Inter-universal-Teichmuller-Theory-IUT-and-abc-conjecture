import tmp.sheaf.xif.paper.S576PositiveQvPhiQOrderFieldsActual
import tmp.sheaf.xif.paper.S561QvPhiMinimalPackageActual
import tmp.sheaf.xif.paper.S583AlignedDivisorEvalS491Actual

/-! # S581: S567 qOrder preimage from S575 positiveUnit

For a minimal package P, qvPhiTriData T and object A, the positive unit has
valuation exponent qOrder.  We build the S567 preimage H and then the S576
positive package and tau. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S581QvPhiPositivePreimageFromS575Actual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S553QvPhiTriDataActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S567QvPhiQOrderFieldsFromTriDataActual
open LeanFormal.IUT.XiFPaper.S491AlignedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S465LiftedDivisorMapActual
open LeanFormal.IUT.XiFPaper.S457DivisorMapActual
open LeanFormal.IUT.XiFPaper.S583AlignedDivisorEvalS491Actual
open LeanFormal.IUT.XiFPaper.S576PositiveQvPhiQOrderFieldsActual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (T : QvPhiTriData (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

noncomputable def s581PositiveUnit (qOrder : ℕ) : (coverField A.base)ˣ :=
  Classical.choose ((P.valuation A.base).valuation_surjective (qOrder : ℤ))

theorem s581PositiveUnit_valuation (qOrder : ℕ) :
    Multiplicative.toAdd ((P.valuation A.base).valuation
      (s581PositiveUnit P A qOrder)) = (qOrder : ℤ) :=
  Classical.choose_spec ((P.valuation A.base).valuation_surjective (qOrder : ℤ))

/-- S556 input induced by the S561 minimal package. -/
abbrev s581InputData : S556InputDataActual (K := K) :=
  s561InputData (K := K) P

/-- Exact eval datum needed for the positive preimage. -/
structure S581PositiveEvalData where
  eval_eq : example32DivisorAlignedS491 (K := K) P.valuation A.base
      (Additive.ofMul (ULift.up
        (s581PositiveUnit P A (T.qOrder A.base)))) =
    Algebra.GrothendieckAddGroup.of
      (ULift.up (T.qOrder A.base) : StageDivisor.{u+1})

/-- Exact missing positive unit divisor evaluation. -/
def S581PositiveEvalRequired : Prop :=
  Nonempty (S581PositiveEvalData (K := K) P T A)

/-- The S567 qOrder preimage constructed from the S575 positive unit and the
exact eval datum. -/
noncomputable def s581QOrderPreimage
    (hEval : S581PositiveEvalData (K := K) P T A) :
    S567QOrderPreimage (K := K) T (s561InputData (K := K) P) A where
  divisor := ULift.up (T.qOrder A.base)
  divisor_eq := rfl
  rationalFunction :=
    Additive.ofMul (ULift.up
      (s581PositiveUnit P A (T.qOrder A.base)))
  divisor_eq' := by
    change example32DivisorAlignedS491 (K := K) P.valuation A.base
        (Additive.ofMul (ULift.up
          (s581PositiveUnit P A (T.qOrder A.base)))) =
      Algebra.GrothendieckAddGroup.of
        (ULift.up (T.qOrder A.base) : StageDivisor.{u+1})
    exact hEval.eval_eq

/-- S576 positive package from the conditional preimage. -/
noncomputable def s581PositiveQvPhiQOrderFields
    (hEval : S581PositiveEvalData (K := K) P T A) :
    S576PositiveQvPhiQOrderFields (K := K) T
      (s561InputData (K := K) P) A :=
  s576PositiveQvPhiQOrderFieldsOfPreimage (K := K) T
    (s561InputData (K := K) P) A (s581QOrderPreimage (K := K) P T A hEval)

/-- Conditional tau with the positive preimage. -/
noncomputable def s581Tau
    (hEval : S581PositiveEvalData (K := K) P T A) :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s567Input (K := K) (s561InputData (K := K) P))) A) :=
  s576Tau (K := K) T (s561InputData (K := K) P) A
    (s581PositiveQvPhiQOrderFields (K := K) P T A hEval)

end LeanFormal.IUT.XiFPaper.S581QvPhiPositivePreimageFromS575Actual

end
