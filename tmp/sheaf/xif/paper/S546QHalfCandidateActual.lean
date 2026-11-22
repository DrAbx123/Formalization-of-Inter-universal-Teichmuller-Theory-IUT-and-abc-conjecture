import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import Mathlib.RingTheory.RootsOfUnity.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S546QHalfCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.NumberFieldFinitePlace

universe u
variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {place : NumberField.FinitePlace K}
variable (parameter : FinitePlaceQCandidate place)

/-- qHalf candidate in the algebraic closure of the completion, chosen from
the old repository root-existence theorem. -/
noncomputable def qHalfRoot :
    (AlgebraicClosure (Completion place))ˣ :=
  Classical.choose (exists_twoLRoot_unit_in_algebraicClosure (l := l) parameter)

/-- The qHalf root has the correct 2l-th power. -/
theorem qHalfRoot_pow :
    qHalfRoot (l := l) parameter ^ (2 * l.value) =
      tateParameterUnit place parameter.q parameter.q_ne_zero :=
  Classical.choose_spec (exists_twoLRoot_unit_in_algebraicClosure (l := l) parameter)

/-- qHalf root candidate data. -/
structure QHalfCandidate where
  root : (AlgebraicClosure (Completion place))ˣ
  root_pow :
    root ^ (2 * l.value) =
      tateParameterUnit place parameter.q parameter.q_ne_zero

noncomputable def qHalfCandidate : QHalfCandidate (l := l) parameter where
  root := qHalfRoot (l := l) parameter
  root_pow := qHalfRoot_pow (l := l) parameter

/-- Ratio of two algebraic-closure qHalf roots is a mu_{2l} root. -/
theorem qHalfRoot_ratio_mem_rootsOfUnity
    {r₁ r₂ : (AlgebraicClosure (Completion place))ˣ}
    (h₁ : r₁ ^ (2 * l.value) =
      tateParameterUnit place parameter.q parameter.q_ne_zero)
    (h₂ : r₂ ^ (2 * l.value) =
      tateParameterUnit place parameter.q parameter.q_ne_zero) :
    r₁ / r₂ ∈ rootsOfUnity (2 * l.value)
      (AlgebraicClosure (Completion place)) := by
  rw [mem_rootsOfUnity]
  rw [div_pow, h₁, h₂]
  simp

/-- Completion-level ratio wrapper using the old repository theorem. -/
theorem completionRoot_ratio_mem_rootsOfUnity
    {r₁ r₂ : (Completion place)ˣ}
    (h₁ : r₁ ^ (2 * l.value) =
      Units.mk0 parameter.q parameter.q_ne_zero)
    (h₂ : r₂ ^ (2 * l.value) =
      Units.mk0 parameter.q parameter.q_ne_zero) :
    r₁ / r₂ ∈ rootsOfUnity (2 * l.value) (Completion place) :=
  qParameterTwoLRootUnit_ratio_mem_rootsOfUnity (l := l) parameter h₁ h₂

end LeanFormal.IUT.XiFPaper.S546QHalfCandidateActual

end
