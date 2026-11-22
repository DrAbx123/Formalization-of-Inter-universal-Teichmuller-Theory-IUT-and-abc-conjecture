/- R2 final: per-row StepV bound for actual row packets `D t` => weighted average => H.

  For each row tuple `t : Fin(j+1) -> iota`, `D t` is the actual packet; the DONE
  `Mzk1G1F2R2ActualInstantiationActual.packetHull_le_collectionChoiceBound (D t)` gives
  `V t = vol(packetHull (D t)) <= collectionChoiceBound ... t slot` (with `et := t`,
  `idag := slot`).  The DONE integration then gives the IV:1585 weighted average <= H once
  `collectionBound ... <= H`.  The LeH side is DONE via
  `Mzk1BoxR2PaperThetaLeHActual.paperThetaWeighted_le`.
  No equality identification; no stub; no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F2R2ActualInstantiationActual
import tmp.sheaf.xif.paper.Mzk1BoxR2IntegrationActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2RowPacketWiringActual

open MeasureTheory
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxActualR2Actual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2IntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2R2ActualInstantiationActual

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

/-- **R2 weighted average <= H for actual row packets**. -/
theorem rowPackets_weightedAverage_le_H
    [Nonempty ι]
    (j : ℕ) (D : (Fin (j + 1) → ι) → PacketHullData (p := p) places tuple (J := J) (E := E))
    (hmu : ∀ t, Measure.IsAddHaarMeasure (D t).mu)
    (lam : ι → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (l iotaL : ℝ) (l_ne_zero : l ≠ 0) (d oq : ι → ℝ) (slot : Fin (j + 1)) (H : ℝ)
    (hslot : ∀ t : Fin (j + 1) → ι, ((j : ℝ) ^ 2 / (2 * l)) * oq (t slot) ≤ LocalFieldLogarithm.localNormOrder p (D t).varpi)
    (hd : ∀ t : Fin (j + 1) → ι, (∑ i, LocalFieldLogarithm.localNormOrder p
        (arithmeticTupleLocalDifferent places tuple i)) ≤ ∑ i, d (t i))
    (hexc : ∀ t : Fin (j + 1) → ι, (∑ i ∈ (D t).exceptional, (3 + Real.log
        (LocalFieldLogarithm.logShellRamificationExponent
          (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ))) ≤
      4 * ((j : ℝ) + 1) * iotaL)
    (hCB : collectionBound l ((∑ e, d e * Real.log (p : ℝ) * lam e) / ∑ e, lam e)
      ((∑ e, oq e * Real.log (p : ℝ) * lam e) / ∑ e, lam e) (Real.log (p : ℝ)) iotaL j ≤ H) :
    (∑ t : Fin (j + 1) → ι,
        arithmeticTupleNormalizedLogVolume places tuple (D t).mu (packetHull (D t)) * W lam t) /
      (∑ t : Fin (j + 1) → ι, W lam t) ≤ H := by
  refine le_trans (actual_weightedAverage_le_collectionBound_via_perRow lam weights_pos
    l (Real.log (p : ℝ)) iotaL l_ne_zero j d oq slot
    (fun t => arithmeticTupleNormalizedLogVolume places tuple (D t).mu (packetHull (D t)))
    (fun t => ?_)) hCB
  haveI := hmu t
  exact packetHull_le_collectionChoiceBound (D := D t) l (Real.log (p : ℝ)) iotaL j t slot d oq (neg_le_neg (hslot t)) (hd t) (hexc t)

#print axioms rowPackets_weightedAverage_le_H

end LeanFormal.IUT.XiFPaper.Mzk1BoxR2RowPacketWiringActual