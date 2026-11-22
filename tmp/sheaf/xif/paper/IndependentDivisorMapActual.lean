import Iut.Foundations.SourceFiniteStageModelFrobenioid
import Iut.Foundations.Frobenioid

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Independent divisor map from a per-cover valuation family -/

namespace LeanFormal.IUT.XiFPaper.IndependentDivisorMapActual

open LeanFormal.IUT
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid
open CategoryTheory

universe u

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {R : GroupLikeAddMonoidOn D IsFSM}
variable (L : D)
variable {ι : Type u} [Fintype ι]

/-- The map `ℤ →+ Grothendieck ℕ` sending `1` to the class of `1`. -/
noncomputable def intToStageDivisorGrothendieck' :
    ℤ →+ Algebra.GrothendieckAddGroup (StageDivisor.{u}) :=
  zmultiplesHom _ (Algebra.GrothendieckAddGroup.of (ULift.up 1))

/-- Independent divisor map attached to a finite per-cover valuation family. -/
noncomputable def divisorMapFromValuations
    (L : D) (valuation : ι → R.obj L →+ ℤ) :
    R.obj L →+ Algebra.GrothendieckAddGroup (StageDivisor.{u}) :=
  ∑ i : ι, (intToStageDivisorGrothendieck'.comp (valuation i))

/-- The value of the unweighted divisor map is the finite sum of the
valuation classes. -/
theorem divisorMapFromValuations_apply
    (L : D) (valuation : ι → R.obj L →+ ℤ) (x : R.obj L) :
    divisorMapFromValuations L valuation x =
      ∑ i : ι, ((valuation i) x) •
        Algebra.GrothendieckAddGroup.of (ULift.up 1) := by
  unfold divisorMapFromValuations intToStageDivisorGrothendieck'
  simp [zmultiplesHom_apply]

/-- Additivity of the independent divisor map. -/
theorem divisorMapFromValuations_add
    (L : D) (valuation : ι → R.obj L →+ ℤ) (x y : R.obj L) :
    divisorMapFromValuations L valuation (x + y) =
      divisorMapFromValuations L valuation x +
        divisorMapFromValuations L valuation y :=
  map_add _ x y

/-- Weighted per-cover version: a weight in the divisor monoid at every cover. -/
noncomputable def divisorMapWithWeights
    (L : D) (weight : ι → StageDivisor.{u})
    (valuation : ι → R.obj L →+ ℤ) :
    R.obj L →+ Algebra.GrothendieckAddGroup (StageDivisor.{u}) :=
  ∑ i : ι,
    (zmultiplesHom (Algebra.GrothendieckAddGroup (StageDivisor.{u}))
      (Algebra.GrothendieckAddGroup.of (weight i))).comp (valuation i)

theorem divisorMapWithWeights_apply
    (L : D) (weight : ι → StageDivisor.{u})
    (valuation : ι → R.obj L →+ ℤ) (x : R.obj L) :
    divisorMapWithWeights L weight valuation x =
      ∑ i : ι, ((valuation i) x) •
        Algebra.GrothendieckAddGroup.of (weight i) := by
  unfold divisorMapWithWeights
  simp

theorem divisorMapWithWeights_add
    (L : D) (weight : ι → StageDivisor.{u})
    (valuation : ι → R.obj L →+ ℤ) (x y : R.obj L) :
    divisorMapWithWeights L weight valuation (x + y) =
      divisorMapWithWeights L weight valuation x +
        divisorMapWithWeights L weight valuation y :=
  map_add _ x y

end LeanFormal.IUT.XiFPaper.IndependentDivisorMapActual

end
