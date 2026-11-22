import tmp.sheaf.xif.paper.Mzk1IutIVProp14iiiBoxConsumerActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic
/-! S1915 instantiation of the abstract Box readout.

The only missing datum is the explicit bridge between the S1915 theta hull and the StepV tensor
readout; no S1902 carrier equivalence is asserted here. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutS1915Actual
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxConsumerActual
universe u v w
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- S1915 data plus the explicit bridge to the StepV tensor readout. -/
structure S1915BoxConsumer
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p) (tuple : (i : ι) -> V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)] where
  data : BoxReadout places tuple
  a0_eq : data.a0 = s1915A0 T
/-- Instantiate the abstract Box readout at `a0 = s1915A0 T`. -/
def boxReadoutOfS1915
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (C : S1915BoxConsumer T places tuple) : BoxReadout places tuple :=
  { C.data with
    a0 := s1915A0 T
    bridge := C.a0_eq.symm.trans C.data.bridge }
/-- The S1915 theta-hull value is bounded by Box (11), with the carrier bridge explicit. -/
theorem s1915A0_le_box_of_bridge
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (C : S1915BoxConsumer T places tuple) :
    s1915A0 T ≤
      (-LocalFieldLogarithm.localNormOrder p C.data.varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ C.data.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) := by
  have h := box_readout_le (boxReadoutOfS1915 T C)
  simpa [boxReadoutOfS1915] using h
/-- Exact single-point missing datum: the S1902 carrier ↔ StepV tensor comparison. -/
def s1902TensorCarrierGap : List String :=
  [ "S1902Carrier T versus ArithmeticTensorTupleBlock places tuple",
    "transport of s1902Hull/s1902LogVolume to arithmeticTupleNormalizedLogVolume" ]
theorem s1902TensorCarrierGap_length : s1902TensorCarrierGap.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutS1915Actual
end
