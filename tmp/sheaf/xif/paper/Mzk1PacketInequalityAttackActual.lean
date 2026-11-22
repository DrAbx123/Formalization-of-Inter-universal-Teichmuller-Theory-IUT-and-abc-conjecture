/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A751: packet inequality attack for SSIneq -/

/- Exact lana statements (repo-root Iut/, read-only; oleans not built here):
* componentVol_leastHull_tensorLogShell_eq (VcI.lean, docstring l.50-55):
  mu^log (hull (tensorLogShell)) = sum_j rho_{c j} * log p, rho_w = logShellRadius,
  I_w <= p^{-rho_w} O_w sharply;
* componentVol_leastHull_tensorLogShell_ge (:286):
  -(sum_j ordp (scalA c j)) * log p <= componentVol leastHull(tensorLogShell);
* componentVol_leastHull_tensorLogShell_le (:300);
* neg_sum_ordp_scalA_mul_log_le_shellExcess (:241), shellExcess_le_neg_sum_ordp_scalB_mul_log (:251);
* hullPacket_finite = sum_c w_c * sum_j rho_{c j} * log p (exact, :689/707);
* logVol_hull_vcI_eq = (sum_i sum^fin hullPacket)/l*, ssIneq_iff_packets restates SSIneq.

Assembly: the ge-bound gives per-packet lower bounds hullPacket_i >= scalALower_i; summing gives
the hull-sum lower bound; the remaining numeric inequality is
  (s - 1) * a * nC <= sum_i sum^fin (weighted scalA lower bounds),  a = |log q|,
which requires the q-pilot/scalA comparison (not present as a lower bound in lana Pilots/VcI).
The reduction below is real arithmetic; the final numeric inequality is an explicit hypothesis. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PacketInequalityAttackActual

def PacketLowerBound (hullPacket scalALower : ℝ) : Prop := scalALower ≤ hullPacket

theorem sum_lower_of_packet_lowers {ι : Type*} (s : Finset ι)
    (hullPacket scalALower : ι → ℝ) (h : ∀ i ∈ s, PacketLowerBound (hullPacket i) (scalALower i)) :
    ∑ i ∈ s, scalALower i ≤ ∑ i ∈ s, hullPacket i :=
  Finset.sum_le_sum h

theorem ssIneq_of_scalA_sum {s a total hullSum ellStar : ℝ} (hell : 0 < ellStar)
    (havg : hullSum = total * ellStar) (hnum : (s - 1) * a ≤ total) :
    (s - 1) * a ≤ hullSum / ellStar := by
  rw [havg]
  have hell' : ellStar ≠ 0 := ne_of_gt hell
  have h : total * ellStar / ellStar = total := by field_simp [hell']
  rw [h]
  exact hnum

def QPilotScalALowerTarget (s a nC scaledTotal : ℝ) : Prop :=
  (s - 1) * a * nC ≤ scaledTotal

end LeanFormal.IUT.XiFPaper.Mzk1PacketInequalityAttackActual
