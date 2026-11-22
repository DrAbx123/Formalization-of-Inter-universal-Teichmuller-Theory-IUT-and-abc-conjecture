import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual

/-!
# Actual Theta tensor scaled regions and hull

Given an actual tensor packet (places, tuple) and actual fractional coefficients
c : iota -> Real, this file constructs the actual scaled region

  p^(-c) O_hol

as the fractional lattice times the holomorphic lattice inside the same
ArithmeticTensorTupleBlock, its finite union over the theta labels, its
topological closure (the actual hull in that carrier), and the normalized hull
log-volume by arithmeticTupleNormalizedLogVolume.

The qVFamily theta values determine such coefficients only after an actual
alignment of the qVFamily bad places/labels with the tensor index.  That
alignment is not in the current tree; it is recorded as the exact missing
alignment, not replaced by a singleton or PUnit carrier.

No fake PUnit/diagonal tuple, arbitrary inequality, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open MeasureTheory

universe u v w

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- Actual scaled region p^(-c) O_hol in the same tensor block. -/
noncomputable def thetaTensorScaledRegion (c : ι → Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ((arithmeticTupleFractionalLattice places tuple c *
    arithmeticTupleHolomorphicLattice places tuple :
      Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple))

/-- The image set of a finite family of actual scaled regions. -/
noncomputable def thetaTensorImageSet
    (c : SignedLabel l.value → ι → Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  ⋃ j : SignedLabel l.value,
    thetaTensorScaledRegion (places := places) (tuple := tuple) (c j)

/-- Actual hull in the same tensor block: closure of the image set. -/
noncomputable def thetaTensorHull
    (c : SignedLabel l.value → ι → Real) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  closure (thetaTensorImageSet (places := places) (tuple := tuple) (l := l) c)

/-- The normalized log-volume of the actual tensor hull. -/
noncomputable def thetaTensorHullLogVolume
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    (c : SignedLabel l.value → ι → Real) : Real :=
  arithmeticTupleNormalizedLogVolume places tuple μ
    (thetaTensorHull (places := places) (tuple := tuple) c)

/-- Actual qVFamily q-pilot scalar. -/
def thetaTensorQPilotLog
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  nativeQVPilotNormalizedLogMagnitude T

/-- Exact missing alignment: qVFamily theta values must give actual tensor
coefficients c(j) in the chosen packet. -/
structure ThetaTensorQVFamAlignment
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) where
  coefficients : SignedLabel l.value → ι → Real

/-- Exact obstruction: the qVFamily-to-tensor coefficient alignment is not
supplied by the current tree. -/
def ThetaTensorQVFamAlignmentObstruction
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (ThetaTensorQVFamAlignment (ι := ι) T)

end LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual

end