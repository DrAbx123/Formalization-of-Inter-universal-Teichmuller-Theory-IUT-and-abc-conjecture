import tmp.sheaf.xif.paper.Mzk1IutIVProp14iiiBoxFormalActual
import Mathlib.Tactic
/-! Readout interface: an abstract theta-hull value `a0` → Box (11).

The S1915 root-extension theta hull is defined on `S1902Carrier T`; the StepV Box theorem is on
`ArithmeticTensorTupleBlock places tuple`.  No concrete carrier equivalence between these two
types is currently proved.  This file therefore exposes the readout with the bridge as an explicit
field, and records the exact missing carrier comparison rather than faking a definitional equality.
The intended instantiation is `a0 = s1915A0 T` with the bridge
`(s1902LogVolume T (s1902Hull T)).toReal = arithmeticTupleNormalizedLogVolume ...`. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxConsumerActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxFormalActual
universe u v w
/-- Explicit readout data: an abstract theta-hull value `a0`, a StepV tensor region and the
carrier bridge between the two normalized log volumes. -/
structure BoxReadout
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p) (tuple : (i : ι) -> V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)] where
  a0 : Real
  mu : Measure (ArithmeticTensorTupleBlock places tuple)
  inst : Measure.IsAddHaarMeasure mu
  istar : ι
  varpi : CommonPrimeCompletion (places istar (tuple istar))
  hvarpi : varpi ≠ 0
  Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  hPhi : ∀ phi, phi ∈ Phi -> ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple ->
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
  exceptional : Finset ι
  small_outside : ∀ i, i ∉ exceptional ->
    LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2
  S : Set (ArithmeticTensorTupleBlock places tuple)
  hSpos : 0 < mu S
  hS : ∀ s, s ∈ S -> ∃ phi, phi ∈ Phi ∧
    ∃ x, x ∈ arithmeticTupleCanonicalUnitReference places tuple ∧
    s = phi (arithmeticTupleTprod places tuple (Function.update 1 istar varpi) * x)
  bridge : a0 = arithmeticTupleNormalizedLogVolume places tuple mu S
/-- The readout value is bounded by the paper's Box (11). -/
theorem box_readout_le
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (C : BoxReadout places tuple)
    [Measure.IsAddHaarMeasure C.mu] :
    C.a0 ≤
      (-LocalFieldLogarithm.localNormOrder p C.varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ C.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) := by
  rw [C.bridge]
  exact LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxFormalActual.prop14iii_box_formal
    places tuple C.mu C.istar C.varpi C.hvarpi
    C.Phi C.hPhi C.exceptional C.small_outside C.hSpos C.hS
/-- The exact missing carrier comparison between the S1915 theta hull and the StepV tensor. -/
def s1902CarrierBridgeMissing : List String :=
  [ "concrete equivalence/identification of S1902Carrier T with ArithmeticTensorTupleBlock places tuple",
    "transport of s1902Hull/s1902LogVolume to arithmeticTupleNormalizedLogVolume under that identification" ]
theorem s1902CarrierBridgeMissing_length : s1902CarrierBridgeMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14iiiBoxConsumerActual
end
