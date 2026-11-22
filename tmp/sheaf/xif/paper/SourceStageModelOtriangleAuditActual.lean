import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Iut.Foundations.SourceFrobenioidModelType

/-! # Stage-model O^triangle audit

The finite-stage model has divisor monoid StageDivisor = ULift ℕ, not zero.
Hence its pre-Frobenioid is NOT group-like in the source sense
(IsGroupLike would force every divisor value to 0).

This refutes triviality of the characteristic splitting for the stage model.
A concrete nonunit O^triangle witness would require a stage unit with nonzero
normalized valuation; that datum is recorded as an exact missing structure and
is not fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.SourceStageModelOtriangleAuditActual

open Iut
open Iut.SourceModelFrobenioid
open Iut.SourceFinitePlaceReconstruction
open Iut.PreFrobenioid

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The stage model is not group-like: its divisor monoid is ULift ℕ and
contains the nonzero value ULift.up 1. -/
theorem stageModel_not_groupLike
    (place : NumberField.FinitePlace K)
    (object : Carrier (stageDivisorialMonoidOn place) (stageModelInput place)) :
    ¬ Iut.PreFrobenioid.IsGroupLike
        (Iut.SourceModelFrobenioid.Carrier.preFrobenioid
          (stageDivisorialMonoidOn place) (stageModelInput place)) object := by
  intro hgroup
  have hvalue := hgroup (ULift.up (1 : Nat) : StageDivisor.{u})
  have hdown := congrArg ULift.down hvalue
  change (1 : Nat) = 0 at hdown
  omega

/-- Exact missing nonunit O^triangle witness: an actual stage unit whose
normalized valuation is a nonzero stage divisor. -/
structure StageModelOtriangleNonunitWitness
    (place : NumberField.FinitePlace K) where
  base : StageBase place
  unit : base.unopˣ
  divisor : StageDivisor.{u}
  divisor_ne_zero : divisor ≠ 0
  valuation_eq : Algebra.GrothendieckAddGroup.of divisor =
    stageModelDivisor place base (Additive.ofMul unit)

/-- Exact missing datum; no witness is asserted. -/
def StageModelOtriangleNonunitWitnessRequired
    (place : NumberField.FinitePlace K) : Prop :=
  Nonempty (StageModelOtriangleNonunitWitness (K := K) place)

end LeanFormal.IUT.XiFPaper.SourceStageModelOtriangleAuditActual

end
