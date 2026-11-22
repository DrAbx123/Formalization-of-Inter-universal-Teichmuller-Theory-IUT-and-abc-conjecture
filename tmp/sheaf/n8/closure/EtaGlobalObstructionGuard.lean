import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Eta global obstruction guard

Exact global obstruction data from the counterexample pattern:

  kappa = deg A,  S = deg Z,  h - Q = S - kappa.

The consumer guard is: kappa = 0 or S >= kappa.  Under this guard, and the
source bound h <= Theta, the global inequality Q <= Theta follows directly.
No arbitrary global morphism is used.

The guard is sharp: with kappa > 0 and S < kappa the data are consistent with
h <= Theta while Q > Theta, so the guard cannot be dropped.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGlobalObstructionGuard

/-- Exact global obstruction data. -/
structure GlobalObstructionData where
  h : ℝ
  Q : ℝ
  Theta : ℝ
  degA : ℕ
  degZ : ℕ
  kappa : ℕ
  S : ℕ
  kappa_eq_degA : kappa = degA
  S_eq_degZ : S = degZ
  hQ_relation : h - Q = (S : ℝ) - (kappa : ℝ)
  h_le_Theta : h ≤ Theta

/-- Consumer guard: only kappa = 0 or S >= kappa permits the global Q <= Theta
conclusion. -/
def ConsumerGuard (D : GlobalObstructionData) : Prop :=
  D.kappa = 0 ∨ D.S ≥ D.kappa

/-- Direct exact formula for the global Q from the obstruction relation. -/
theorem Q_eq_h_sub_S_add_kappa (D : GlobalObstructionData) :
    D.Q = D.h - (D.S : ℝ) + (D.kappa : ℝ) := by
  linarith [D.hQ_relation]

/-- The guarded consumer conclusion: global Q <= Theta. -/
theorem global_Q_le_Theta_of_guard
    (D : GlobalObstructionData) (hg : ConsumerGuard D) :
    D.Q ≤ D.Theta := by
  have hQ := Q_eq_h_sub_S_add_kappa D
  rcases hg with hk | hSk
  · have hS : (0 : ℝ) ≤ (D.S : ℝ) := by exact_mod_cast Nat.zero_le D.S
    rw [hk] at hQ
    norm_num at hQ
    linarith [D.h_le_Theta]
  · have hsk : (D.kappa : ℝ) ≤ (D.S : ℝ) := by exact_mod_cast hSk
    linarith [D.h_le_Theta]

/-- Sharp counterexample: the unguarded data have h <= Theta but Q > Theta. -/
def sharpCounterexample : GlobalObstructionData where
  h := 0
  Q := 1
  Theta := 0
  degA := 1
  degZ := 0
  kappa := 1
  S := 0
  kappa_eq_degA := rfl
  S_eq_degZ := rfl
  hQ_relation := by norm_num
  h_le_Theta := by norm_num

/-- The sharp counterexample is not guarded. -/
theorem sharpCounterexample_not_guard : ¬ ConsumerGuard sharpCounterexample := by
  intro hg
  rcases hg with hk | hSk
  · norm_num [sharpCounterexample] at hk
  · norm_num [sharpCounterexample] at hSk

/-- The sharp counterexample violates the consumer conclusion. -/
theorem sharpCounterexample_Q_gt_Theta :
    sharpCounterexample.Theta < sharpCounterexample.Q := by
  norm_num [sharpCounterexample]

/-- Structural form: if S < kappa then Q = h + (kappa - S) with positive excess. -/
theorem Q_eq_h_add_excess_of_S_lt_kappa
    (D : GlobalObstructionData) (_hSk : D.S < D.kappa) :
    D.Q = D.h + ((D.kappa : ℝ) - (D.S : ℝ)) := by
  have hQ := Q_eq_h_sub_S_add_kappa D
  linarith

end LeanFormal.IUT.N8Closure.EtaGlobalObstructionGuard
