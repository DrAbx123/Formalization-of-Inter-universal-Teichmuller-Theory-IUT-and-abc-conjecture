import tmp.sheaf.n8.closure.P6Comparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-!
# Eta hull -> ellOut alignment attempt

Actual normalization identity on the canonical tensor hull:

  arithmeticTupleNormalizedLogVolume places tuple mu hull
    = (1 / finrank) * arithmeticTupleHullUnitLogVolume places tuple.

P6 SourceAllowedOutput.ellOut is the C6 degree-normalized log-volume of the
T11 theta-image region J.region, so it carries the 1/finrank normalization and
the C6 hull/measure data.  An equality with the unnormalized unit-relative
canonical-hull volume would require at least: J.region = canonical hull,
matching C6 normalized volume, and finrank = 1.  No such production theorem is
present.

The exact missing alignment is recorded; no arbitrary Theta or aligned value
is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open MeasureTheory
open scoped NumberField

namespace LeanFormal.IUT.N8Closure.EtaHullToEllOutAlignmentAttempt

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- Actual production normalization relation on the canonical hull. -/
theorem normalizedLogVolume_canonicalHull_eq
    :
    arithmeticTupleNormalizedLogVolume places tuple mu
        (arithmeticTupleCanonicalHull places tuple) =
      (1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)) *
        arithmeticTupleHullUnitLogVolume places tuple := by
  unfold arithmeticTupleNormalizedLogVolume
  rw [arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal places tuple mu]
  ring

/-- Exact missing alignment statement: the unit-relative canonical hull volume
equals the P6 source-allowed output ellOut for every output. -/
def MissingHullEllOutAlignment : Prop :=
  ∀ {l : PrimeGeFive} (X : N8NativeInput l) (J : SourceAllowedOutput X),
    arithmeticTupleHullUnitLogVolume J.C3.tensorPlaces J.C3.tensorTuple = J.ellOut

end LeanFormal.IUT.N8Closure.EtaHullToEllOutAlignmentAttempt
