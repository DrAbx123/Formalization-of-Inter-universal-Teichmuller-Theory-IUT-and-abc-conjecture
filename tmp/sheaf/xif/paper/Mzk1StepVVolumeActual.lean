import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import tmp.sheaf.xif.paper.S3014StepVProcessionAverageActual
import tmp.sheaf.xif.paper.S3029StepVAlignmentActual
import Mathlib.Tactic

/-!
# Mzk1StepVVolumeActual

Task-116: actual per-label StepV image region and its normalized log-volume.

Region:
  stepVRegion label := thetaTensorScaledRegion (fun i =>
    if i = istar then stepVLambda p label jValue l else 0)

Its normalized log-volume, under the actual fractional scaling data, is
  -((sum_i c_i) * log p) = -stepVLambda * log p = S3029StepVTerm label.

Thus the volume identity is reduced to the actual scaling datum
ArithmeticTuplePureFractionalScalingData for this one-factor coefficient.
That datum is the exact remaining source object; it is NOT asserted here.

Exceptional set:
  ramifiedExceptional := {i | p - 2 < logShellRamificationExponent_i}
and S3029ExceptionalTerm is by definition the sum over the supplied Finset;
passing ramifiedExceptional gives the paper exceptional set exactly.

No sorry/axiom/True/PUnit/toy.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

/-- The paper exceptional set: ramification exponent > p - 2. -/
noncomputable def ramifiedExceptional : Finset ι := by
  classical
  exact Finset.univ.filter (fun i =>
    (p - 2) < logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- The actual per-label StepV region: coefficient stepVLambda only at istar. -/
noncomputable def stepVRegion
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (l label : Nat) : Set (ArithmeticTensorTupleBlock places tuple) :=
  thetaTensorScaledRegion (p := p) places tuple
    (fun i => if i = istar then stepVLambda p label jValue l else 0)

/-- The exact remaining scaling datum: actual localGenerator data for the
one-factor StepV coefficient stepVLambda. -/
noncomputable def stepVScalingCoefficient
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (l label : Nat) : ι -> Real :=
  fun i => if i = istar then stepVLambda p label jValue l else 0

/-- Conditional volume identity: with actual scaling data for the StepV
coefficient, the region's normalized log-volume is S3029StepVTerm. -/
theorem stepVRegion_volume_eq_of_scalingData
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure mu]
    (label : Nat)
    (data : ArithmeticTuplePureFractionalScalingData (p := p) places tuple
      (stepVScalingCoefficient places tuple istar jValue l label)) :
    arithmeticTupleNormalizedLogVolume places tuple mu
        (stepVRegion places tuple istar jValue l label) =
      S3029StepVTerm places tuple istar jValue l label := by
  unfold stepVRegion S3029StepVTerm
  change arithmeticTupleNormalizedLogVolume places tuple mu
      (thetaTensorScaledRegion places tuple
        (stepVScalingCoefficient places tuple istar jValue l label)) =
    -stepVLambda p label jValue l * Real.log (p : Real)
  unfold thetaTensorScaledRegion
  rw [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (p := p) places tuple mu data]
  have hsum : (∑ i : ι,
      stepVScalingCoefficient places tuple istar jValue l label i) =
      stepVLambda p label jValue l := by
    unfold stepVScalingCoefficient
    simp
  rw [hsum]
  ring

/-- The exceptional term with the paper exceptional set is exactly the sum over
ramification exponents > p-2. -/
theorem S3029ExceptionalTerm_ramified :
    S3029ExceptionalTerm places tuple (ramifiedExceptional (p := p) places tuple) =
      ∑ i ∈ ramifiedExceptional (p := p) places tuple,
        (3 + Real.log (logShellRamificationExponent
          (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  rfl

#check stepVScalingCoefficient
#check stepVRegion
#check stepVRegion_volume_eq_of_scalingData
#check ramifiedExceptional
#check S3029ExceptionalTerm_ramified

end LeanFormal.IUT.XiFPaper.Mzk1StepVVolumeActual

end
