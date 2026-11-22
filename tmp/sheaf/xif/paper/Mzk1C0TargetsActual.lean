/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A918 / C0 targets: target statements for ind2Term and archDefect (source-level)

**Status: PARTIAL**
Reason: the conditional-form target theorems (T1, T1', T2) are green, but they depend on
two lana lemmas that are NOT formalized: `TensorAutCommutationDefect` (tensorAut/theta
commutation) and `TensorMetricOrthogonality` (tensor-metric orthogonality), plus the exact
`componentVol_leastHull_tensorLogShell_eq` formula.

## 试金石回答 (touchstone, C0 = calculator-evidence stage)
This stage does NOT contain an inequality claim.  Quantifier/information-entry statement:
the results are CONDITIONAL on the explicit predicates below; no `forall D` inequality and
no numerical bound is asserted.  Therefore the touchstone question
('what inequality does this stage claim?') is answered: **not applicable / deferred**
(本轮不含不等式主张，不适用/暂缓).

## 试金石（3^k−1）模板回答

试金石：本阶段不主张不等式；试金石仅在其数据被 A3/B1/C3 定理化时适用，届时在相应主张中回答（本轮：不适用/暂缓）。

## 判定句
**C0 = PARTIAL，停在该判定点。**  -/

/- lana source (read-only; root Iut/ tree, oleans not built here):
* `Iut/WallEquiv/Gap.lean:747-754` defines
    `ind2Term D i p c = componentVol (leastHull (thetaComponent)) -
                        componentVol (scaleElt • leastHull (shell))`;
  `ind2Term_nonneg` (:756), `ind2Term_eq_zero` off bad chars (:771);
  `gapHullAt` (:895) = sum_c w_c * ind2Term; `gap_eq` (:961);
  file header (:30-36): Ind2 automorphisms are `tensorAut` (Z_p-lattice automorphisms of
  factor log-shells) and 'need not commute with theta values'; sign at bad primes OPEN.
* `Gap.lean:459` defines
    `archDefect c = componentVol (leastHull (logShell)) - componentVol (logShell)`;
  `archDefect_nonneg` (:463); exact value `log((2^{N-1})!)/2^N` stated at :66 as NOT
  formalized (needs orthogonality of tensor-metric components).

This file gives the TARGET statements in conditional form: arithmetic consequences of the
two missing lana inputs (no sorry/axiom/assumption replacing proofs; the lana inputs are
explicit hypotheses). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C0TargetsActual

/-- **Target T1 (Ind2 scaling term)**: from the lana-shaped definition
`ind2Term = thetaHullLog - scaledHullLog` and the two componentVol values
(`thetaHullLog = base + (j^2*v_p(q)/(2l))*logp + defect`, `scaledHullLog = base`),
conclude `ind2Term = (j^2*v_p(q)/(2l))*logp + defect`. -/
theorem ind2Term_eq_scaling_add_defect {ind2 thetaHullLog scaledHullLog base vp j l logp defect : ℝ}
    (hdef : ind2 = thetaHullLog - scaledHullLog)
    (hθ : thetaHullLog = base + (j ^ 2 * vp / (2 * l)) * logp + defect)
    (hscaled : scaledHullLog = base) :
    ind2 = (j ^ 2 * vp / (2 * l)) * logp + defect := by
  rw [hdef, hθ, hscaled]
  ring

/-- **Target T1' (fractional-part form)**: if the commutation defect is
`defect = frac * logp` with `0 <= frac < 1`, then `ind2Term` equals the fractional-part
expression `((j^2*v_p(q)/(2l)) + frac) * logp`. -/
theorem ind2Term_frac_form {ind2 thetaHullLog scaledHullLog base vp j l logp frac : ℝ}
    (hdef : ind2 = thetaHullLog - scaledHullLog)
    (hθ : thetaHullLog = base + (j ^ 2 * vp / (2 * l)) * logp + frac * logp)
    (hscaled : scaledHullLog = base) :
    ind2 = ((j ^ 2 * vp / (2 * l)) + frac) * logp := by
  rw [hdef, hθ, hscaled]
  ring

/-- **Target T2 (archDefect exact value)**: from the lana-shaped definition
`archDefect = leastHullLog - shellLog` and the orthogonality-input
`leastHullLog = shellLog + log((2^{N-1})!)/2^N`, conclude the exact value. -/
theorem archDefect_eq_formula {archDefectValue leastHullLog shellLog : ℝ} {N : ℕ}
    (hdef : archDefectValue = leastHullLog - shellLog)
    (horth : leastHullLog = shellLog +
      Real.log ((Nat.factorial (2 ^ (N - 1)) : ℝ)) / ((2 : ℝ) ^ N)) :
    archDefectValue = Real.log ((Nat.factorial (2 ^ (N - 1)) : ℝ)) / ((2 : ℝ) ^ N) := by
  rw [hdef, horth]
  ring

/-- The orthogonality input needed for T2, as an explicit predicate. -/
def TensorMetricOrthogonality (leastHullLog shellLog : ℝ) (N : ℕ) : Prop :=
  leastHullLog = shellLog + Real.log ((Nat.factorial (2 ^ (N - 1)) : ℝ)) / ((2 : ℝ) ^ N)

/-- The tensorAut commutation-defect input needed for T1, as an explicit predicate. -/
def TensorAutCommutationDefect (thetaHullLog base vp j l logp defect : ℝ) : Prop :=
  thetaHullLog = base + (j ^ 2 * vp / (2 * l)) * logp + defect

def c0TargetRows : List (String × String × String) :=
  [ ("ind2Term definition", "Gap.lean:747-754 (difference of componentVols)", "LANA SOURCE") ,
    ("T1 ind2Term_eq_scaling_add_defect", "conditional arithmetic", "PROVED") ,
    ("T1' ind2Term_frac_form", "fractional-part form", "PROVED (conditional)") ,
    ("T2 archDefect_eq_formula", "exact value log((2^{N-1})!)/2^N", "PROVED (conditional)") ,
    ("TensorMetricOrthogonality", "needed lana orthogonality input", "GAP (lana)") ,
    ("TensorAutCommutationDefect", "needed tensorAut/theta commutation input", "GAP (lana)") ,
    ("componentVol_leastHull_tensorLogShell_eq", "exact hull formula (lana)", "LANA (oleans)") ,
    ("thetaComponent definition/closure", "theta component = union over tensorAut", "LANA (oleans)") ,
    ("E-C0-1 TensorAutCommutationDefect", "tensorAut Z_p-lattice action vs theta exchange defect", "EXTERNAL / TO PROVE (lana)") ,
    ("E-C0-2 TensorMetricOrthogonality", "leastHullLog = shellLog + formula", "EXTERNAL / TO PROVE (lana)") ,
    ("E-C0-3 componentVol_leastHull_tensorLogShell_eq", "exact hull volume sum_j rho log p", "EXTERNAL / TO PROVE (lana)") ]

theorem c0TargetRows_length : c0TargetRows.length = 11 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C0TargetsActual
