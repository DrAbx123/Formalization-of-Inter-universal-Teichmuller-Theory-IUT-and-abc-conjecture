import tmp.sheaf.xif.paper.S553QvPhiTriDataActual
import tmp.sheaf.xif.paper.S556QvPhiInputActual
import tmp.sheaf.xif.paper.S563QvOrderElementConstructionActual

/-! # S567: QvPhiQOrderFields from S553 qOrder + S556 divisor map

The zero divisor/identity rational function gives an actual QvPhiQOrderFields.
For the positive qOrder generator, an effective preimage and rational function
are recorded as exact missing data when not supplied. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S567QvPhiQOrderFieldsFromTriDataActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S553QvPhiTriDataActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (T : QvPhiTriData (K := K))
variable (D : S556InputDataActual (K := K))
variable (A : Object (qvPhi (K := K) D.ramification))

/-- S556 input with divisor map from the valuation family. -/
abbrev s567Input : Input (qvPhi (K := K) D.ramification) :=
  s556InputActual (K := K) D

/-- Actual QvPhiQOrderFields: zero divisor and identity rational function. -/
noncomputable def s567ZeroQvPhiQOrderFields :
    QvPhiQOrderFields (K := K) D.ramification (s567Input (K := K) D) A where
  divisor := 0
  rationalFunction := 0
  divisor_eq := by
    change (s567Input (K := K) D).divisor A.base 0 =
      Algebra.GrothendieckAddGroup.of
        (0 : ((qvPhi (K := K) D.ramification).obj A.base).carrier)
    rw [map_zero]
    simp

/-- Exact preimage data for the positive qOrder generator at A.base: an
effective divisor equal to ULift.up (qOrder A.base) and a rational function
whose divisor is that divisor. -/
structure S567QOrderPreimage where
  divisor : ((qvPhi (K := K) D.ramification).obj A.base).carrier
  divisor_eq : divisor =
    (ULift.up (T.qOrder A.base) :
      ((qvPhi (K := K) D.ramification).obj A.base).carrier)
  rationalFunction : (s567Input (K := K) D).rationalFunctions.obj A.base
  divisor_eq' : (s567Input (K := K) D).divisor A.base rationalFunction =
    Algebra.GrothendieckAddGroup.of divisor

/-- Exact missing qOrder preimage. -/
def S567QOrderPreimageRequired : Prop :=
  Nonempty (S567QOrderPreimage (K := K) T D A)

/-- Conditional QvPhiQOrderFields from a qOrder preimage. -/
noncomputable def s567QvPhiQOrderFieldsOfPreimage
    (H : S567QOrderPreimage (K := K) T D A) :
    QvPhiQOrderFields (K := K) D.ramification (s567Input (K := K) D) A where
  divisor := H.divisor
  rationalFunction := H.rationalFunction
  divisor_eq := H.divisor_eq'

/-- The zero fields have zero divisor. -/
theorem s567ZeroQvPhiQOrderFields_divisor :
    (s567ZeroQvPhiQOrderFields (K := K) D A).divisor = 0 := rfl

/-- The qOrder generator is positive at every base object. -/
theorem s567QOrder_pos (X : Example32SmallBase K) : 0 < T.qOrder X :=
  T.qOrder_pos X

end LeanFormal.IUT.XiFPaper.S567QvPhiQOrderFieldsFromTriDataActual

end
