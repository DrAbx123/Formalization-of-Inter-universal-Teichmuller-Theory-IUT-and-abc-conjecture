import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import tmp.sheaf.xif.paper.S1446ReportCReadoutActual
import Mathlib.Tactic
/-! Actual-packet Box readout for IUT IV Prop 1.4(iii).

The bound is the hull version
`arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound` (StepVAssembly:814), applied to
the actual `ArithmeticTensorTupleBlock`, its actual different generators and the actual
field-product decomposition `e`.  The signed local readout `V = (log μ(S)-log μ(O))/dim` is
recorded separately; no `s1915A0` truncation is used. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
/-- Actual packet data for the StepV hull bound. -/
structure PacketHullData
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p) (tuple : (i : ι) -> V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type (max u v)} [Finite J] {E : J -> Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)] where
  mu : Measure (ArithmeticTensorTupleBlock places tuple)
  inst : Measure.IsAddHaarMeasure mu
  e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)
  istar : ι
  varpi : CommonPrimeCompletion (places istar (tuple istar))
  hvarpi : varpi ≠ 0
  Phi : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple)
  hPhi_ne : Phi.Nonempty
  hPhi : ∀ phi, phi ∈ Phi -> ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple ->
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
  exceptional : Finset ι
  small_outside : ∀ i, i ∉ exceptional ->
    LocalFieldLogarithm.logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2
/-- The actual hull whose normalized log-volume is bounded by Box (11). -/
def packetHull
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type (max u v)} [Finite J] {E : J -> Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (D : PacketHullData places tuple (J := J) (E := E)) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  arithmeticTupleHolomorphicHull places tuple D.e
    (arithmeticTupleStepVPossibleImages places tuple D.istar D.varpi D.Phi)
/-- The actual-packet hull bound (hull version of StepV (v)). -/
theorem packetHull_normalizedLogVolume_le_box
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type (max u v)} [Finite J] {E : J -> Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (D : PacketHullData places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu] :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
      (packetHull (places := places) (tuple := tuple) D) ≤
      (-LocalFieldLogarithm.localNormOrder p D.varpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ D.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound places tuple D.mu D.e
    D.istar D.varpi D.hvarpi D.Phi D.hPhi_ne D.hPhi D.exceptional D.small_outside
/-- Actual signed local readout `V = (log μ(S)-log μ(O))/dim`; kept unnormalized by any
paper average and never truncated with `ENNReal.ofReal`. -/
noncomputable def signedLocalReadout {X : Type*} [MeasurableSpace X]
    (mu : Measure X)
    (S O : Set X) (dim : Real) : Real :=
  (Real.log (mu S).toReal - Real.log (mu O).toReal) / dim
/-- Exact single-point missing datum: S1902 carrier ↔ actual tensor block / per-factor signed sum. -/
def s1902SignedReadoutGap : List String :=
  [ "S1902Carrier T versus ArithmeticTensorTupleBlock at fixed (p,j,tuple)",
    "per-factor signed sum = actual hull unit log volume (StepV decomposition)" ]
theorem s1902SignedReadoutGap_length : s1902SignedReadoutGap.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
end
