/- R2 actual instantiation: V (paper Theta row hull normalized log volume) <= collectionChoiceBound.

  `V := arithmeticTupleNormalizedLogVolume places tuple D.mu (packetHull D)` is the actual
  paper Theta row hull log-volume; the DONE `Mzk1BoxReadoutLocalActual.packetHull_normalizedLogVolume_le_box`
  gives `V <= (-lambda + sum_i d_i + 1) log p + sum_{i in exceptional} (3 + log e_i)`
  (StepVAssembly:814 instantiated at the actual `(places, tuple, e, varpi, Phi)`).
  The queued inequality bridge `paperBound_le_collectionChoiceBound` then gives
  `V <= collectionChoiceBound`, requiring only
    hlam : -(j^2/(2l)) oq(et idag) <= -lambda   (from R2PerRowSupplyActual.lambdaFromQ_ge_slot),
    hD   : sum_i d_i <= sum_i d (et i),
    hexc : exceptional sum <= 4(j+1) iotaL        (from R2PerRowSupplyActual.exceptionalSum_le_four_mul),
    hlogp : 0 <= log p.
  hlam/hD/hexc are explicit hypotheses here (the remaining paper-to-Section-1 data);
  no fake.  No stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.xif.paper.Mzk1G1R2RowSupplySupportActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2ActualInstantiationActual

open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R2RowSupplySupportActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage

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

/-- **R2 actual row box bound**: the actual paper Theta row hull log-volume
    `V = arithmeticTupleNormalizedLogVolume μ (packetHull D)` is at most the
    `collectionChoiceBound`, under the paper parameter inequalities. -/
theorem packetHull_le_collectionChoiceBound
    (D : PacketHullData (p := p) places tuple (J := J) (E := E))
    [Measure.IsAddHaarMeasure D.mu]
    (l logp iotaL : ℝ) (j : ℕ) (et : Fin (j + 1) → ι) (idag : Fin (j + 1))
    (d oq : ι → ℝ)
    (hlam : -LocalFieldLogarithm.localNormOrder p D.varpi ≤
      -(((j : ℝ) ^ 2 / (2 * l)) * oq (et idag)))
    (hD : (∑ i, LocalFieldLogarithm.localNormOrder p
        (arithmeticTupleLocalDifferent places tuple i)) ≤ ∑ i, d (et i))
    (hexc : (∑ i ∈ D.exceptional, (3 + Real.log
        (LocalFieldLogarithm.logShellRamificationExponent
          (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ))) ≤
      4 * ((j : ℝ) + 1) * iotaL) :
    arithmeticTupleNormalizedLogVolume places tuple D.mu
        (packetHull (places := places) (tuple := tuple) D) ≤ 
      (-(((j : ℝ) ^ 2 / (2 * l)) * oq (et idag)) + ∑ i, d (et i) + 1) * Real.log (p : ℝ) +
        4 * ((j : ℝ) + 1) * iotaL := by
  have hlogp : 0 ≤ Real.log (p : ℝ) := by
    have hp2 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Fact.out : p.Prime).one_lt
    exact le_of_lt (Real.log_pos hp2)
  have hV := packetHull_normalizedLogVolume_le_box (p := p) (places := places)
    (tuple := tuple) (J := J) (E := E) D
  exact le_trans hV (Mzk1G1R2RowSupplySupportActual.paperBound_le_collectionChoiceBound l (Real.log (p : ℝ)) iotaL
    (LocalFieldLogarithm.localNormOrder p D.varpi)
    (∑ i, LocalFieldLogarithm.localNormOrder p
      (arithmeticTupleLocalDifferent places tuple i))
    (∑ i ∈ D.exceptional, (3 + Real.log
      (LocalFieldLogarithm.logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)))
    (oq (et idag)) (∑ i, d (et i)) j hlogp hlam hD hexc)

#print axioms packetHull_le_collectionChoiceBound

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2ActualInstantiationActual