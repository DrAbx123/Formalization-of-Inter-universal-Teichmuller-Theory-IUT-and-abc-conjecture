/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # Mzk1Chain1JetActual — §14 chain 1 (arithmetic Kodaira–Spencer) interface draft (A878)

Paper-level design objects (NOT known objects in the repo):
* capsule `j`'s `(j+1)`-fold tensor packet is read as a `j`-jet: filtration `F^j` and graded
  piece `gr^j`; the graded degrees are `-(j+1)·D` (inverse-different side) and `-j²·A`
  (theta-value side);
* for `σ ∈ Gal(K/F)` not preserving the multiplicative line, `κ_σ : gr^a → gr^b` is the
  non-commutativity of the σ-action with the filtration;
* **integrality defect** of `κ_σ` at a place `w` with normalized `ord_w(q)`, tame shell
  exponent `h_w`: `defect = (j²−j′²)·ord_w(q)/(2l)` in `log p` units, against the shell
  allowance `h_w·log p`.  The hidden condition of the chain is: defect ≤ allowance at every
  `V`-place (so that `κ_σ` is integral and the non-zero integral morphism gives the degree
  inequality).

This file freezes the arithmetic core and the decision experiment for the concrete curve
`E : y² + xy = x³ + 5` over `ℚ_5` (repo: `ConcreteSplitCurvePadic`, split multiplicative at
`p = 5`, `v_5(Δ) = 1`, `c₄` a unit, `e = f = 1`, tame shell exponent `h = 1−1/e = 0`).
Result: at the unique `V`-place the defect is positive while the shelf allowance is `0`;
hence `κ_σ` is **not integral** there and the chain's hidden condition fails in this
concrete case (tame split reduction).  A ramified place with `e ≥ 3` could absorb the
defect only for restricted `(j,j′)` (threshold below); no ramified `V`-place exists for the
rational curve at `p = 5`.  Therefore chain 1 is **rejected** in this decision experiment.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Chain1JetActual

/-! ### 1. Graded degrees of the jet / theta / hull sides -/

/-- graded degree of the inverse-different side of the `j`-th jet (abstract `D`). -/
def gradedHullDegree (j : ℕ) (D : ℝ) : ℝ := -((j : ℝ) + 1) * D

/-- graded degree of the theta side of the `j`-th jet (abstract `A`). -/
def gradedThetaDegree (j : ℕ) (A : ℝ) : ℝ := -((j : ℝ) ^ 2) * A

/-! ### 2. κ_σ integrality defect and shell allowance -/

/-- Integrality defect of `κ_σ : gr^j → gr^{j'}` at a place with normalized `ord(q)`. -/
def kappaDefect (j j' : ℕ) (ordq : ℝ) (l : ℕ) : ℝ :=
  (((j : ℝ) ^ 2 - (j' : ℝ) ^ 2) * ordq) / (2 * (l : ℝ))

/-- Shell allowance at a place with ramification index `e`: tame value `1 - 1/e` times `log p`. -/
def hullAllowance (e : ℕ) (logp : ℝ) : ℝ := (1 - 1 / (e : ℝ)) * logp

/-- The hidden condition of chain 1: at every `V`-place the defect is absorbed by the shell. -/
def Absorbed (j j' : ℕ) (ordq logp : ℝ) (e l : ℕ) : Prop :=
  kappaDefect j j' ordq l ≤ hullAllowance e logp

/-! ### 3. Concrete decision data: E : y²+xy = x³+5 at p = 5, l = 7 -/

/-- `v_5(Δ) = 1`, so the normalized q-order is `1` (repo: `concreteSplitCurveLocal_delta_*`). -/
def ordqAtFive : ℝ := 1

/-- `log 5 > 0`. -/
theorem log_five_pos : (0 : ℝ) < Real.log 5 := Real.log_pos (by norm_num)

/-- Tame shell exponent at `p = 5`: `e = 1`, hence allowance `0`. -/
theorem hullAllowance_five : hullAllowance 1 (Real.log 5) = 0 := by
  unfold hullAllowance
  norm_num

/-- Defect for `(j,j') = (2,1)`, `l = 7`, `ord(q)=1` is `(4−1)/14 = 3/14 > 0`. -/
theorem kappaDefect_two_one_five : kappaDefect 2 1 ordqAtFive 7 = 3 / 14 := by
  unfold kappaDefect ordqAtFive
  norm_num

/-- **Decision at `p = 5`**: the defect is positive whereas the shell allowance is zero, so
the absorption condition fails (κ_σ is not integral at the `V`-place). -/
theorem tame_five_not_absorbed : ¬ Absorbed 2 1 ordqAtFive (Real.log 5) 1 7 := by
  unfold Absorbed
  rw [kappaDefect_two_one_five, hullAllowance_five]
  norm_num

/-! ### 4. Ramified threshold (conditional survival branch) -/

/-- For a ramified place with `e ≥ 3` and `log p > 0`, absorption is possible for the
moderate defect `(2²−1²) = 3` with `l = 7` only if `1 − 1/e ≥ 3/(14 log p)`; stated as the
exact threshold. -/
theorem ramified_absorption_iff (e : ℕ) (he : 0 < e) (logp : ℝ) (hlog : 0 < logp) :
    Absorbed 2 1 1 logp e 7 ↔ (3 / 14 : ℝ) ≤ (1 - 1 / (e : ℝ)) * logp := by
  unfold Absorbed kappaDefect hullAllowance
  norm_num

/-! ### 5. Rows -/

def chain1Rows : List (String × String) :=
  [ ("jet reading: gr^j degrees −(j+1)D vs −j²A", "DEFINED"),
    ("κ_σ integrality defect formula", "DEFINED"),
    ("shell allowance h_w·log p (tame 1−1/e)", "DEFINED"),
    ("concrete E: y²+xy=x³+5, p=5, l=7: defect 3/14 > 0, allowance 0", "PROVED"),
    ("absorption fails at the V-place (tame split case)", "PROVED (rejection)"),
    ("ramified threshold e ≥ 3 conditional survival", "DEFINED (Iff)"),
    ("Gaussian-pole cancellation at full places (§9)", "INPUT (paper)"),
    ("chain 1 verdict: rejected on the decision experiment", "DECISION") ]

theorem chain1Rows_length : chain1Rows.length = 8 := rfl

#check tame_five_not_absorbed
#check ramified_absorption_iff
#check chain1Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1Chain1JetActual
end
