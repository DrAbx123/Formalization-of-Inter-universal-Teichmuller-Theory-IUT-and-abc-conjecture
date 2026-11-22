/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# q-pilot log-volume comparison for the Tate j-invariant

This module relates the exact norm results for the canonical Tate q-series
j-invariant (module `TateJInvariantNorm`) to the logarithmic volume of the
q-pilot used in the IUT III §3.12 comparison chain.

The q-pilot logarithmic volume of the canonical local parameter is

`qPilotLogVolume l = -log ‖q l‖`,

which is `log l.value` since `‖q l‖ = l.value⁻¹`.  The j-invariant
logarithmic norm is

`tateJInvariantLogVolume l = log ‖tateJInvariant l‖`.

The comparison proved here is exactly

`log ‖j‖ = -log ‖q‖`,

equivalently `log ‖j‖ + log ‖q‖ = 0` and `‖j‖ * ‖q‖ = 1`, and both sides
equal `log l.value`.  The statements are the q-pilot specialization at the
level of p-adic norms and real logarithms.  No log-volume of a general
Θ-pilot object is defined or bounded here, no Tate uniformization is
asserted, and `q` is not replaced by the inverse of `j`.
-/

namespace LeanFormal.IUT

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

section LogVolumes

/-- The q-pilot logarithmic volume `-log ‖q l‖` of the canonical Tate
parameter.  Since `‖q l‖ = l.value⁻¹`, this equals `log l.value`. -/
def qPilotLogVolume : ℝ := - Real.log ‖q l‖

/-- The logarithmic norm `log ‖tateJInvariant l‖` of the Tate j-invariant. -/
def tateJInvariantLogVolume : ℝ := Real.log ‖tateJInvariant l‖

@[simp] theorem qPilotLogVolume_eq_neg_log_q_norm :
    qPilotLogVolume l = - Real.log ‖q l‖ := rfl

@[simp] theorem tateJInvariantLogVolume_eq_log_j_norm :
    tateJInvariantLogVolume l = Real.log ‖tateJInvariant l‖ := rfl

/-- The q-pilot logarithmic volume is `log l.value`. -/
theorem qPilotLogVolume_eq_log_prime :
    qPilotLogVolume l = Real.log (l.value : ℝ) := by
  rw [qPilotLogVolume, q_norm_eq, Real.log_inv]
  ring

/-- The j-invariant logarithmic norm is also `log l.value`. -/
theorem tateJInvariantLogVolume_eq_log_prime :
    tateJInvariantLogVolume l = Real.log (l.value : ℝ) := by
  rw [tateJInvariantLogVolume, tateJInvariant_norm_eq_prime]

/-- The comparison of the two log-volumes: the j-invariant log-volume equals
the q-pilot log-volume. -/
theorem tateJInvariantLogVolume_eq_qPilotLogVolume :
    tateJInvariantLogVolume l = qPilotLogVolume l := by
  rw [tateJInvariantLogVolume_eq_log_prime,
    qPilotLogVolume_eq_log_prime]

/-- The additive form of the comparison: `log ‖j‖ + log ‖q‖ = 0`. -/
theorem tateJInvariantLogVolume_add_log_q_norm :
    tateJInvariantLogVolume l + Real.log ‖q l‖ = 0 := by
  rw [tateJInvariantLogVolume, tateJInvariant_norm, Real.log_inv]
  ring

/-- The comparison as a vanishing difference. -/
theorem tateJInvariantLogVolume_sub_qPilotLogVolume :
    tateJInvariantLogVolume l - qPilotLogVolume l = 0 := by
  rw [tateJInvariantLogVolume_eq_qPilotLogVolume]
  ring

theorem qPilotLogVolume_pos : 0 < qPilotLogVolume l := by
  rw [qPilotLogVolume_eq_log_prime]
  apply Real.log_pos
  have h : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  linarith

theorem tateJInvariantLogVolume_pos : 0 < tateJInvariantLogVolume l := by
  rw [tateJInvariantLogVolume_eq_qPilotLogVolume]
  exact qPilotLogVolume_pos l

/-- The multiplicative norm comparison, restated for the log-volume consumer:
`‖j‖ * ‖q‖ = 1`. -/
theorem tateJInvariant_norm_mul_q_norm_one :
    ‖tateJInvariant l‖ * ‖q l‖ = 1 :=
  tateJInvariant_norm_mul_q_norm l

end LogVolumes

section ComparisonPacket

/-- Consumer-facing packet for the III §3.12 q-pilot comparison: the exact
norms of `q` and `j`, together with the log-volume identity
`log ‖j‖ = -log ‖q‖`. -/
structure TateQPilotLogComparisonPacket where
  qNorm : ℝ
  qNorm_eq : qNorm = ‖q l‖
  qNorm_pos : 0 < qNorm
  qNorm_lt_one : qNorm < 1
  jNorm : ℝ
  jNorm_eq : jNorm = ‖tateJInvariant l‖
  jNorm_eq_inv_qNorm : jNorm = qNorm⁻¹
  jNorm_eq_prime : jNorm = (l.value : ℝ)
  jNorm_gt_one : 1 < jNorm
  jNorm_mul_qNorm : jNorm * qNorm = 1
  qLogVolume : ℝ
  qLogVolume_eq : qLogVolume = qPilotLogVolume l
  jLogVolume : ℝ
  jLogVolume_eq : jLogVolume = tateJInvariantLogVolume l
  jLogVolume_eq_qLogVolume : jLogVolume = qLogVolume
  jLogVolume_add_log_qNorm : jLogVolume + Real.log qNorm = 0
  qLogVolume_eq_log_prime : qLogVolume = Real.log (l.value : ℝ)
  qLogVolume_pos : 0 < qLogVolume

def tateQPilotLogComparisonPacket : TateQPilotLogComparisonPacket l where
  qNorm := ‖q l‖
  qNorm_eq := rfl
  qNorm_pos := q_norm_pos l
  qNorm_lt_one := q_norm_lt_one l
  jNorm := ‖tateJInvariant l‖
  jNorm_eq := rfl
  jNorm_eq_inv_qNorm := tateJInvariant_norm l
  jNorm_eq_prime := tateJInvariant_norm_eq_prime l
  jNorm_gt_one := tateJInvariant_norm_gt_one l
  jNorm_mul_qNorm := tateJInvariant_norm_mul_q_norm l
  qLogVolume := qPilotLogVolume l
  qLogVolume_eq := rfl
  jLogVolume := tateJInvariantLogVolume l
  jLogVolume_eq := rfl
  jLogVolume_eq_qLogVolume := tateJInvariantLogVolume_eq_qPilotLogVolume l
  jLogVolume_add_log_qNorm := tateJInvariantLogVolume_add_log_q_norm l
  qLogVolume_eq_log_prime := qPilotLogVolume_eq_log_prime l
  qLogVolume_pos := qPilotLogVolume_pos l

theorem tateQPilotLogComparisonPacket_qNorm :
    (tateQPilotLogComparisonPacket l).qNorm = ‖q l‖ := rfl

theorem tateQPilotLogComparisonPacket_qNorm_pos :
    0 < (tateQPilotLogComparisonPacket l).qNorm :=
  (tateQPilotLogComparisonPacket l).qNorm_pos

theorem tateQPilotLogComparisonPacket_qNorm_lt_one :
    (tateQPilotLogComparisonPacket l).qNorm < 1 :=
  (tateQPilotLogComparisonPacket l).qNorm_lt_one

theorem tateQPilotLogComparisonPacket_jNorm :
    (tateQPilotLogComparisonPacket l).jNorm = ‖tateJInvariant l‖ := rfl

theorem tateQPilotLogComparisonPacket_jNorm_eq_inv_qNorm :
    (tateQPilotLogComparisonPacket l).jNorm =
      ((tateQPilotLogComparisonPacket l).qNorm)⁻¹ :=
  (tateQPilotLogComparisonPacket l).jNorm_eq_inv_qNorm

theorem tateQPilotLogComparisonPacket_jNorm_eq_prime :
    (tateQPilotLogComparisonPacket l).jNorm = (l.value : ℝ) :=
  (tateQPilotLogComparisonPacket l).jNorm_eq_prime

theorem tateQPilotLogComparisonPacket_jNorm_gt_one :
    1 < (tateQPilotLogComparisonPacket l).jNorm :=
  (tateQPilotLogComparisonPacket l).jNorm_gt_one

theorem tateQPilotLogComparisonPacket_jNorm_mul_qNorm :
    (tateQPilotLogComparisonPacket l).jNorm *
      (tateQPilotLogComparisonPacket l).qNorm = 1 :=
  (tateQPilotLogComparisonPacket l).jNorm_mul_qNorm

theorem tateQPilotLogComparisonPacket_qLogVolume :
    (tateQPilotLogComparisonPacket l).qLogVolume = qPilotLogVolume l := rfl

theorem tateQPilotLogComparisonPacket_jLogVolume :
    (tateQPilotLogComparisonPacket l).jLogVolume =
      tateJInvariantLogVolume l := rfl

theorem tateQPilotLogComparisonPacket_jLogVolume_eq_qLogVolume :
    (tateQPilotLogComparisonPacket l).jLogVolume =
      (tateQPilotLogComparisonPacket l).qLogVolume :=
  (tateQPilotLogComparisonPacket l).jLogVolume_eq_qLogVolume

theorem tateQPilotLogComparisonPacket_jLogVolume_add_log_qNorm :
    (tateQPilotLogComparisonPacket l).jLogVolume +
      Real.log (tateQPilotLogComparisonPacket l).qNorm = 0 :=
  (tateQPilotLogComparisonPacket l).jLogVolume_add_log_qNorm

theorem tateQPilotLogComparisonPacket_qLogVolume_eq_log_prime :
    (tateQPilotLogComparisonPacket l).qLogVolume =
      Real.log (l.value : ℝ) :=
  (tateQPilotLogComparisonPacket l).qLogVolume_eq_log_prime

theorem tateQPilotLogComparisonPacket_qLogVolume_pos :
    0 < (tateQPilotLogComparisonPacket l).qLogVolume :=
  (tateQPilotLogComparisonPacket l).qLogVolume_pos

/-- The complete q-pilot comparison output for III §3.12: the exact norms,
the multiplicative relation, and the additive log-volume identity. -/
theorem tateQPilotLogComparisonPacket_summary :
    (tateQPilotLogComparisonPacket l).jNorm =
        ((tateQPilotLogComparisonPacket l).qNorm)⁻¹ ∧
      (tateQPilotLogComparisonPacket l).jNorm *
        (tateQPilotLogComparisonPacket l).qNorm = 1 ∧
      (tateQPilotLogComparisonPacket l).jLogVolume =
        (tateQPilotLogComparisonPacket l).qLogVolume ∧
      (tateQPilotLogComparisonPacket l).jLogVolume +
        Real.log (tateQPilotLogComparisonPacket l).qNorm = 0 ∧
      (tateQPilotLogComparisonPacket l).qLogVolume =
        Real.log (l.value : ℝ) :=
  ⟨tateQPilotLogComparisonPacket_jNorm_eq_inv_qNorm l,
    tateQPilotLogComparisonPacket_jNorm_mul_qNorm l,
    tateQPilotLogComparisonPacket_jLogVolume_eq_qLogVolume l,
    tateQPilotLogComparisonPacket_jLogVolume_add_log_qNorm l,
    tateQPilotLogComparisonPacket_qLogVolume_eq_log_prime l⟩

end ComparisonPacket

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateQPilotJComparison : Obligation :=
  { id := "IUTIII.Corollary312.tate-q-pilot-j-comparison"
    source := "IUT III, Corollary 3.12 q-pilot comparison chain (local norm/log-volume input)"
    status := VerificationStatus.proved
    note :=
      "For q equal to p in Q_p, p >= 5, the q-pilot log-volume -log||q|| " ++
        "and the log of the Tate j-invariant norm satisfy log||j|| = " ++
        "-log||q||, i.e. ||j|| * ||q|| = 1, and both equal log p. This is the " ++
        "q-pilot specialization at the level of p-adic norms and real " ++
        "logarithms; it defines no general Theta-pilot log-volume, asserts no " ++
        "Tate uniformization, and does not identify q with j^{-1}."
    dependsOn :=
      [ "Foundations.Geometry.tate-j-invariant-norm" ] }

end LeanFormal.IUT.Audit
