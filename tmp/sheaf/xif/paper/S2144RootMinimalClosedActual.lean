import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S2144RootMinimalClosedActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open MeasureTheory
variable {K : Type} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable (c : ι → Real)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- Given the paper root coefficient scaling data, the root minimal region is
the multiplicative translate of the compact open canonical unit reference, hence
compact. -/
theorem s2144_isCompact_rootMinimalRegion_of_data
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    IsCompact (thetaTensorScaledRegion (p := p) (places := places) (tuple := tuple) c) := by
  unfold thetaTensorScaledRegion
  rw [arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    (p := p) (places := places) (tuple := tuple) (c := c) data]
  let u : (ArithmeticTensorTupleBlock places tuple)ˣ :=
    arithmeticTupleFractionalGeneratorUnit places tuple data
  have hcompact := (isCompact_arithmeticTupleCanonicalRegions places tuple).2
  exact hcompact.image (by
    change Continuous (fun x : ArithmeticTensorTupleBlock places tuple =>
      (u : ArithmeticTensorTupleBlock places tuple) * x)
    exact (LinearMap.mulLeft ℚ_[p] (u : ArithmeticTensorTupleBlock places tuple)).continuous_of_finiteDimensional)
/-- Conditional closedness of the root minimal region from scaling data. -/
theorem s2144_isClosed_rootMinimalRegion_of_data
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    IsClosed (thetaTensorScaledRegion (p := p) (places := places) (tuple := tuple) c) :=
  (s2144_isCompact_rootMinimalRegion_of_data (p := p) places tuple c data).isClosed
end LeanFormal.IUT.XiFPaper.S2144RootMinimalClosedActual
end
