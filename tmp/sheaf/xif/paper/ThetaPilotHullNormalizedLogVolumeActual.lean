import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual

/-!
# Theta-pilot hull normalized log-volume and qVFamily q-pilot scalar

The actual normalized Haar log-volume is

  arithmeticTupleNormalizedLogVolume places tuple μ
    (arithmeticTupleCanonicalHull places tuple),

using the actual canonical hull, unit reference and additive Haar measure from
FinitePlaceArithmeticTupleCanonicalHull.  Its positivity/finiteness comes from
the actual measure theorem on the canonical regions.

The qVFamily q-pilot scalar is the actual normalized magnitude
nativeQVPilotNormalizedLogMagnitude T.

The scalar comparison qPilotLog <= ThetaHullLog is stated exactly; no inequality
is asserted.  The exact missing fractional-lattice realization of qPilotLog is
recorded separately.

No PUI/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.ThetaPilotHullNormalizedLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
open LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual

universe u v w

variable {K : Type u} [Field K] [NumberField K]
variable {l : PrimeGeFive}
variable {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]

/-- Actual normalized Theta-pilot hull log-volume from the canonical hull. -/
def thetaHullLog : Real :=
  arithmeticTupleNormalizedLogVolume places tuple μ
    (arithmeticTupleCanonicalHull places tuple)

/-- The actual ThetaHullLog is the normalized relative hull log-volume. -/
theorem thetaHullLog_eq_relative :
    thetaHullLog (places := places) (tuple := tuple) μ =
      (1 / (Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple) : ℝ)) *
        arithmeticTupleHullUnitLogVolume places tuple := by
  unfold thetaHullLog arithmeticTupleNormalizedLogVolume
  rw [arithmeticTupleCanonicalRegions_relativeLogVolume places tuple μ]

/-- The canonical hull has positive finite actual Haar measure. -/
theorem thetaHullLog_measure_pos_lt_top :
    0 < μ (arithmeticTupleCanonicalHull places tuple) ∧
      μ (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1

/-- Actual qVFamily q-pilot scalar (normalized magnitude). -/
def qPilotLog (T : SourceNativeInitialThetaData.{0} l) : Real :=
  nativeQVPilotNormalizedLogMagnitude T

/-- The q-pilot scalar is the actual qVFamily normalized magnitude. -/
theorem qPilotLog_eq (T : SourceNativeInitialThetaData.{0} l) :
    qPilotLog T = nativeQVPilotNormalizedLogMagnitude T := rfl

/-- Exact target scalar comparison qPilotLog <= thetaHullLog. -/
def qPilotThetaHullLogComparison
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  qPilotLog T <= thetaHullLog (places := places) (tuple := tuple) μ

/-- The comparison target unfolds to the actual scalars. -/
theorem qPilotThetaHullLogComparison_iff
    (T : SourceNativeInitialThetaData.{0} l) :
    qPilotThetaHullLogComparison (places := places) (tuple := tuple) μ T ↔
      nativeQVPilotNormalizedLogMagnitude T <=
        thetaHullLog (places := places) (tuple := tuple) μ :=
  Iff.rfl

/-- Exact missing fractional-lattice realization of qPilotLog by the qVFamily
q-pilot fractional lattice. -/
structure QVPilotFractionalLatticeRealization
    (T : SourceNativeInitialThetaData.{0} l) where
  coefficients : ι → Real
  data : ArithmeticTuplePureFractionalScalingData places tuple coefficients
  realizedLog : Real
  realizedLog_eq : realizedLog = qPilotLog T
  fractionalLatticeLog_eq :
    arithmeticTupleNormalizedLogVolume places tuple μ
      ((arithmeticTupleFractionalLattice places tuple coefficients *
        arithmeticTupleHolomorphicLattice places tuple :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) = realizedLog

/-- Exact obstruction: no actual qVFamily fractional-lattice data is supplied
for this tensor packet. -/
def QVPilotFractionalLatticeObstruction
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (QVPilotFractionalLatticeRealization (places := places) (tuple := tuple) μ T)

/-- Conditional qPilotLog realization from explicit fractional-lattice data. -/
theorem qPilotLog_eq_fractionalLattice_of_realization
    (T : SourceNativeInitialThetaData.{0} l)
    (R : QVPilotFractionalLatticeRealization (places := places) (tuple := tuple) μ T) :
    R.realizedLog = qPilotLog T :=
  R.realizedLog_eq

end LeanFormal.IUT.XiFPaper.ThetaPilotHullNormalizedLogVolumeActual

end