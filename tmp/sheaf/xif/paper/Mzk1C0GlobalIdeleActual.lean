import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import Mathlib.Tactic

/-!
# C0 source B: bad-component + good-component idele data

This replaces the failed total `if/choose` function by the definitional bad
component family (q_v at each bad lift), a good-component family outside the
finite bad support, and arch=1.  All bad equalities are rfl; no dependent
Classical.choose cast is used.

Remaining gap: idele height/readout (second missing arrow), not constructed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1C0GlobalIdeleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Finite support of the bad lifts. -/
noncomputable def c0BadSupport : Finset (NumberField.FinitePlace T.arithmetic.F) := by
  classical
  exact Finset.univ.image (fun b => (nativeBadLift T).lift b)

/-- Bad-component data: q_v at each bad lift, good components outside the
finite support, arch components 1. -/
structure C0GlobalIdeleData where
  bad : (b : Bad (nativePlaceSelection T)) →
    NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b)
  bad_eq : ∀ b, bad b = (qVFamily T b).q
  good : (v : NumberField.FinitePlace T.arithmetic.F) →
    v ∉ c0BadSupport T → (NumberFieldFinitePlace.Completion v)ˣ
  arch : (w : NumberField.InfinitePlace T.arithmetic.F) → (w.Completion)ˣ

/-- Actual C0 idele data: bad=q_v (definitional), good=1, arch=1. -/
noncomputable def c0GlobalIdeleData : C0GlobalIdeleData T where
  bad := fun b => (qVFamily T b).q
  bad_eq := fun _ => rfl
  good := fun _ _ => 1
  arch := fun _ => 1

theorem c0GlobalIdeleData_bad (b : Bad (nativePlaceSelection T)) :
    (c0GlobalIdeleData T).bad b = (qVFamily T b).q := rfl

theorem c0GlobalIdeleData_bad_eq (b : Bad (nativePlaceSelection T)) :
    (c0GlobalIdeleData T).bad b = (qVFamily T b).q :=
  (c0GlobalIdeleData T).bad_eq b

theorem c0GlobalIdeleData_good_one
    (v : NumberField.FinitePlace T.arithmetic.F)
    (hv : v ∉ c0BadSupport T) :
    (c0GlobalIdeleData T).good v hv = 1 := rfl

theorem c0GlobalIdeleData_arch_one
    (w : NumberField.InfinitePlace T.arithmetic.F) :
    (c0GlobalIdeleData T).arch w = 1 := rfl

#print axioms c0GlobalIdeleData_bad_eq
#print axioms c0GlobalIdeleData_good_one
#print axioms c0GlobalIdeleData_arch_one

end LeanFormal.IUT.XiFPaper.Mzk1C0GlobalIdeleActual
