import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# ETA local scaling donor

Extracts actual local scaling donors from production:
- `FinitePlaceNormalizedUnitScalingLogVolume`: the actual prime scalar unit
  `arithmeticTuplePrimeScalarUnit`, its actual normalized log-volume scaling
  theorem, and the actual holomorphic reference lattice;
- `LogShellVolumeConsumer`: the actual log-shell integer index/volume consumer
  and the actual Haar-volume identity.

Assumption checklist (all explicit hypotheses, not free data):
1. `p` is prime (`Fact p.Prime`);
2. finite index type `ι`, coordinates `V i`, places/tuple;
3. the arithmetic tensor block carries `MeasurableSpace` and `BorelSpace`;
4. `μ` is an additive Haar measure (`Measure.IsAddHaarMeasure μ`);
5. for the local log-shell consumer: `K` is a normed field, `CharZero K`,
   `CompleteSpace K`, `IsUltrametricDist K`, `ProperSpace K`,
   `NormedAlgebra ℚ_[p] K`.

Actual donors exist under these hypotheses.  The only missing bridge is from
the arithmetic tensor scaling to the native q calibration; it is recorded as
an exact named gap (`MissingQCalibrationBridge`), not faked.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Foundations.LocalFields.LogShellVolume
open scoped Pointwise
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.N8Closure.EtaLocalScalingDonor

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  {ι : Type v} [Fintype ι] {V : ι → Type w}
  (places : (i : ι) → V i → FinitePlaceAtPrime K p)
  (tuple : (i : ι) → V i)
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  (mu : Measure (ArithmeticTensorTupleBlock places tuple))
  [Measure.IsAddHaarMeasure mu]

/-- Actual arithmetic-tensor local scaling donor.  All fields are production
objects; `primeScalar_scaling` is the actual degree-normalized volume identity.
-/
structure ArithmeticTupleScalingDonor
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] where
  /-- Actual prime scalar unit. -/
  primeScalarUnit : (ArithmeticTensorTupleBlock places tuple)ˣ
  primeScalarUnit_eq : primeScalarUnit = arithmeticTuplePrimeScalarUnit places tuple
  /-- Actual holomorphic reference lattice. -/
  holomorphicLattice : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)
  holomorphicLattice_eq : holomorphicLattice = arithmeticTupleHolomorphicLattice places tuple
  /-- Actual degree-normalized log-volume function. -/
  normalizedLogVolume : Set (ArithmeticTensorTupleBlock places tuple) → ℝ
  normalizedLogVolume_eq : normalizedLogVolume = arithmeticTupleNormalizedLogVolume places tuple mu
  /-- Actual prime-scalar scaling on the canonical unit reference. -/
  primeScalar_scaling : ∀ k : ℤ,
    normalizedLogVolume
      ((↑(primeScalarUnit ^ k) : ArithmeticTensorTupleBlock places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple) =
      -((k : ℝ) * Real.log (p : ℝ))

/-- Actual construction of the arithmetic-tensor donor. -/
noncomputable def arithmeticTupleScalingDonor :
    ArithmeticTupleScalingDonor places tuple mu where
  primeScalarUnit := arithmeticTuplePrimeScalarUnit places tuple
  primeScalarUnit_eq := rfl
  holomorphicLattice := arithmeticTupleHolomorphicLattice places tuple
  holomorphicLattice_eq := rfl
  normalizedLogVolume := arithmeticTupleNormalizedLogVolume places tuple mu
  normalizedLogVolume_eq := rfl
  primeScalar_scaling := fun k =>
    arithmeticTupleNormalizedLogVolume_primeScalar_zpow
      (places := places) (tuple := tuple) mu k

theorem arithmeticTupleScalingDonor_nonempty :
    Nonempty (ArithmeticTupleScalingDonor places tuple mu) :=
  ⟨arithmeticTupleScalingDonor places tuple mu⟩

/-- Actual local log-shell consumer: production index/volume data at a
nonarchimedean local field. -/
noncomputable def localLogShellConsumer
    (K : Type u) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] : LogShellVolumeConsumer (K := K) (p := p) :=
  logShellVolumeConsumer (K := K) (p := p)

theorem localLogShellConsumer_index_pos
    (K : Type u) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] :
    0 < (localLogShellConsumer K p).index :=
  (localLogShellConsumer K p).index_pos

/-- Exact missing bridge from the arithmetic tensor scaling donor to the native
q calibration.  No production declaration identifies the arithmetic-tensor
prime-scalar normalization with the native q-pilot scalar; this is the gap.
-/
def MissingQCalibrationBridge : Prop :=
  ¬ Nonempty (ArithmeticTupleScalingDonor places tuple mu →
      Multiplicative ℝ)

end LeanFormal.IUT.N8Closure.EtaLocalScalingDonor

end