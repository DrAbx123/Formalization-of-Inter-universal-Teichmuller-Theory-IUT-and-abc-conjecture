/- R2 row assembly: actual paper Theta row hull log-volume <= collectionChoiceBound.

  Compose the DONE `Mzk1BoxReadoutLocalActual.packetHull_normalizedLogVolume_le_box`
  (`V <= (-lambda + dsum + 1) logp + exc`, StepVAssembly:814 at the actual packet) with the
  DONE `Mzk1BoxR2InequalityBridgeActual.packetHull_le_collectionChoiceBound`
  (inequality bridge: lambda >= slot, dsum <= sum d, exc <= 4(j+1) iota, logp >= 0),
  at the actual packet data `D : PacketHullData` and the actual row data `et, d, oq`.
  The hD comparison is the queued `Mzk1G1F2R2RowDataActual.hD_of_surjective` shape and is
  kept as an explicit hypothesis here (remaining actual source data).
  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.xif.paper.Mzk1BoxR2InequalityBridgeActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2RowVAssemblyActual

open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2InequalityBridgeActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p}
variable {tuple : (i : ι) → V i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- **R2 row: V <= collectionChoiceBound** at the actual packet `D`. -/
theorem rowV_le_collectionChoiceBound
    (D : PacketHullData (p := p) places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu]
    {E' : Type u} [Fintype E'] (l iotaL : ℝ) (j : ℕ)
    (d oq : E' → ℝ) (et : Fin (j + 1) → E') (idag : Fin (j + 1))
    (hslot : (j : ℝ) ^ 2 / (2 * l) * oq (et idag) ≤
      LocalFieldLogarithm.localNormOrder p D.varpi)
    (hd : (∑ i, LocalFieldLogarithm.localNormOrder p
        (arithmeticTupleLocalDifferent places tuple i)) ≤ ∑ i, d (et i))
    (hexc : (∑ i ∈ D.exceptional, (3 + Real.log
        (LocalFieldLogarithm.logShellRamificationExponent
          (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ))) ≤
      4 * ((j : ℝ) + 1) * iotaL) :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
        (packetHull (places := places) (tuple := tuple) D) ≤ 
      collectionChoiceBound l (Real.log (p : ℝ)) iotaL j d oq et idag := by
  have hlogp : 0 ≤ Real.log (p : ℝ) := by
    have hp2 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Fact.out : p.Prime).one_lt
    exact le_of_lt (Real.log_pos hp2)
  have hV := packetHull_normalizedLogVolume_le_box (p := p) (places := places)
    (tuple := tuple) (J := J) (E := E) D
  exact packetHull_le_collectionChoiceBound (E := E') l (Real.log (p : ℝ)) iotaL j d oq et idag
    (arithmeticTupleNormalizedLogVolume places tuple D.mu
      (packetHull (places := places) (tuple := tuple) D))
    (LocalFieldLogarithm.localNormOrder p D.varpi)
    (∑ i, LocalFieldLogarithm.localNormOrder p
      (arithmeticTupleLocalDifferent places tuple i))
    (∑ i ∈ D.exceptional, (3 + Real.log
      (LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)))
    hV hslot hd hexc hlogp

#print axioms rowV_le_collectionChoiceBound

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2RowVAssemblyActual