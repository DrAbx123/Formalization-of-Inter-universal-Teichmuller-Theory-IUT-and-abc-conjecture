import tmp.sheaf.xif.paper.Mzk1BoxDistinguishedScalarActual
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
/-! Putting the distinguished theta scalar into `PacketHullData.varpi`.

The local-field identification `varpi = completionMap (theta alpha j)` is explicit; the
Box hull bound itself is the already-proved actual-packet theorem. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedVarpiActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
universe u v w
/-- Replace the distinguished scalar field of actual packet data. -/
def packetHullDataWithVarpi
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type (max u v)} [Finite J] {E : J -> Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (D : PacketHullData places tuple (J := J) (E := E))
    (varpi : CommonPrimeCompletion (places D.istar (tuple D.istar))) (hvarpi : varpi ≠ 0) :
    PacketHullData places tuple (J := J) (E := E) :=
  { D with varpi := varpi, hvarpi := hvarpi }
/-- Box (11) after replacing the distinguished scalar by the actual theta value. -/
theorem packetHull_with_theta_varpi
    {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
    {places : (i : ι) -> V i -> FinitePlaceAtPrime K p} {tuple : (i : ι) -> V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type (max u v)} [Finite J] {E : J -> Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (D : PacketHullData places tuple (J := J) (E := E))
    (thetaVarpi : CommonPrimeCompletion (places D.istar (tuple D.istar)))
    (htheta_ne_zero : thetaVarpi ≠ 0)
    [Measure.IsAddHaarMeasure D.mu] :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
      (packetHull (places := places) (tuple := tuple)
        (packetHullDataWithVarpi D thetaVarpi htheta_ne_zero)) ≤
      (-LocalFieldLogarithm.localNormOrder p thetaVarpi +
          ∑ i, LocalFieldLogarithm.localNormOrder p
            (arithmeticTupleLocalDifferent places tuple i) + 1) * Real.log p +
        ∑ i ∈ D.exceptional, (3 + Real.log
          (LocalFieldLogarithm.logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real)) :=
  by
  letI : Measure.IsAddHaarMeasure
      (packetHullDataWithVarpi D thetaVarpi htheta_ne_zero).mu := D.inst
  exact packetHull_normalizedLogVolume_le_box
    (packetHullDataWithVarpi D thetaVarpi htheta_ne_zero)
end LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedVarpiActual
end
