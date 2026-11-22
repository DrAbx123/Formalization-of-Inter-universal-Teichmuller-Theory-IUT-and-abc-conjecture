import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateRealLineLogCompatibility
import Mathlib.Data.Nat.Prime.Basic

/-!
  # Log-Frobenius compatibility of log-volumes on the real-line test carrier
  (outsider survey continuation: [AbsTopIII] Corollary 5.10, (ii))

  The original statement ([AbsTopIII] = "Topics in Absolute Anabelian Geometry
  III", corpus text :8594-8598; OCR spacing/quotes normalized) reads:

    "(ii) (Log-Frobenius Compatibility of Log-volumes) For v, S as in (i), the
    log-volume (respectively, radial log-volume), computed "at ⋎ ∈ L", is
    compatible [cf. part (c) of Proposition 5.7, (i), (ii)], relative to the
    relevant log-homotopy, with the log-volume (respectively, angular
    log-volume), computed "at ⋎+1 ∈ L"."

  Minimal fragment on the test carrier, annotated per ingredient:

  * proved: `realLineLogHomotopy` -- the affine log-domain segment
    `s |-> (n + s) * log |c|` between consecutive labeled computations, with
    continuity (`realLineLogHomotopy_continuous`) and affinity
    (`realLineLogHomotopy_affine`) in the path parameter;
  * proved: `realLineLogShellLogVolume_homotopy_interpolation` -- along the
    dilation family `c ^ (n + s)` (c > 0) the measured log-volume of the
    dilated log-shell equals the homotopy value; test-carrier form of the
    log-image link of Proposition 5.7, (i), (c) (:7952-7960);
  * proved: `realLineLogShellLogVolume_logFrobenius_compatibility` -- the
    log-volume computed at the label `n + 1` differs from the computation at
    `n` by exactly the step weight `dot-mu-log(c)`, uniformly in the label
    (`realLineLogHomotopy_iterate` is the iterated form);
  * reduced: the label set `L` (with successor) is modeled by `R` with `+ 1`;
    the "relevant log-homotopy" is realized only as the affine log-domain
    segment above; "computed at ⋎ / at ⋎+1" are the parameter values `0 / 1`;
  * additional data (not available on this carrier): the ambient shell-homotopy
    formalism ([AbsTopIII] Definition 5.9, (ii) domain), the label set `L`
    itself, and the radial/angular decomposition.

  The same file promotes the step value `-f * n * log p` of Proposition 5.7,
  (i), (a) (corpus :7932-7935) from the earlier test values `f = 1, p = 2`
  (`realLineLogShellLogVolume_half_pow`) to general `f` and positive real `p`:

  * `realLineDilationLogWeight_frobeniusStep`: the weight of the contracting
    step `p ^ (-f)` is `-(f * log p)`;
  * `realLineLogShellLogVolume_frobeniusStep_pow` (integer labels) and
    `realLineLogShellLogVolume_frobeniusStep_increment` (label-independent
    increment `-(f * log p)`);
  * `realLineLogShellLogVolume_primeFrobeniusStep_increment` packages this
    with a genuine prime `P : Nat.Prime P`; the primality hypothesis is
    present for narrative fidelity and is not used by the real computation;
  * `realLineLogShellLogVolume_primeStep_two` is the consistency instance
    recovering the previous `f = 1, p = 2` step for integer labels.

  Reductions (do not overclaim): the carrier is the additive line with
  dilation, not a local field with its multiplicative group; `p` and `f` enter
  only through the real modulus `p ^ (-f)` and the real number `log p`; no
  residue-field degree, norm, or prime arithmetic is modeled; the arithmetic
  log-volume of [AbsTopIII] is not realized; the literal carrier and the
  value-level boundary are untouched.

  Evidence: `tmp/outsider-survey-iq-carrier-20261016/` logs and the landing
  report `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`,
  section 17.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.HaarTranslateModel.RealLine

noncomputable section

open MeasureTheory
open scoped Pointwise

/-! ## 1. The log-homotopy on the test carrier -/

/-- The label-indexed affine log-homotopy: the straight segment in
log-coordinates between consecutive labeled computations, `(n + s) * log |c|`.
This is the test-carrier minimal model of the "relevant log-homotopy" of
[AbsTopIII] Corollary 5.10, (ii) (corpus :8594-8598); the label is modeled by
the real parameter `n` and "computed at label / label + 1" by the parameter
values `s = 0 / 1` of this value function. -/
def realLineLogHomotopy (c : ℝ) (n s : ℝ) : ℝ := (n + s) * Real.log |c|

/-- Continuity of the log-homotopy in the path parameter: the minimal
path-continuity content of the homotopy structure. -/
theorem realLineLogHomotopy_continuous (c n : ℝ) :
    Continuous fun s : ℝ => realLineLogHomotopy c n s := by
  unfold realLineLogHomotopy
  exact ((continuous_const : Continuous fun _ : ℝ => n).add continuous_id).mul
    (continuous_const : Continuous fun _ : ℝ => Real.log |c|)

/-- Affinity of the log-homotopy in the path parameter: the value function is
the affine segment through the label-`n` computation with slope
`dot-mu-log(c) = log |c|`. -/
theorem realLineLogHomotopy_affine (c n s : ℝ) :
    realLineLogHomotopy c n s = n * Real.log |c| + s * Real.log |c| := by
  unfold realLineLogHomotopy
  ring

/-- **Interpolation**: along the dilation family `c ^ (n + s)` (`c > 0`), the
measured log-volume of the dilated log-shell equals the homotopy value -- the
test-carrier form of the log-image link of [AbsTopIII] Proposition 5.7, (i),
(c) (:7952-7960): the log-volume computed along the segment is the
log-coordinate `(n + s) * log c` of the dilation. -/
theorem realLineLogShellLogVolume_homotopy_interpolation (c : ℝ) (hc : 0 < c)
    (n s : ℝ) :
    Real.log (normalizedRealLineVolume ((c ^ (n + s)) • unitInterval)).toReal =
      realLineLogHomotopy c n s := by
  rw [realLineLogShellLogVolume_dilation (c ^ (n + s)), realLineDilationLogWeight,
    abs_of_pos (Real.rpow_pos_of_pos hc (n + s)), Real.log_rpow hc,
    realLineLogHomotopy, abs_of_pos hc]

/-- **Consecutive-label step**: the homotopy value at the label `n + 1` exceeds
the value at the label `n` by exactly the step weight
`dot-mu-log(c) = log |c|`. -/
theorem realLineLogHomotopy_step (c n : ℝ) :
    realLineLogHomotopy c n 1 - realLineLogHomotopy c n 0 =
      realLineDilationLogWeight c := by
  unfold realLineLogHomotopy realLineDilationLogWeight
  ring

/-- **Log-Frobenius compatibility** ([AbsTopIII] Corollary 5.10, (ii), corpus
:8594-8598; minimal fragment): the log-volume computed at the label `n + 1`
along the log-homotopy is compatible with the computation at `n` -- their
difference is the Frobenius step weight `dot-mu-log(c)`, uniformly in the
label `n`. -/
theorem realLineLogShellLogVolume_logFrobenius_compatibility (c : ℝ) (hc : 0 < c)
    (n : ℝ) :
    Real.log (normalizedRealLineVolume ((c ^ (n + 1)) • unitInterval)).toReal -
      Real.log (normalizedRealLineVolume ((c ^ n) • unitInterval)).toReal =
        realLineDilationLogWeight c := by
  have h1 := realLineLogShellLogVolume_homotopy_interpolation c hc n 1
  have h0 : Real.log (normalizedRealLineVolume ((c ^ n) • unitInterval)).toReal =
      realLineLogHomotopy c n 0 := by
    simpa using realLineLogShellLogVolume_homotopy_interpolation c hc n 0
  rw [h1, h0, realLineLogHomotopy_step]

/-- Iterated steps: the value at the label `n + k` exceeds the value at `n` by
`k` copies of the step weight -- the uniformity in the label in iterative
form. -/
theorem realLineLogHomotopy_iterate (c n : ℝ) (k : ℕ) :
    realLineLogHomotopy c (n + k) 0 =
      realLineLogHomotopy c n 0 + (k : ℝ) * Real.log |c| := by
  unfold realLineLogHomotopy
  ring

/-! ## 2. The step value `-(f * n * log p)` for general `f`, `p` -/

/-- The weight of the contracting Frobenius step `p ^ (-f)` (`p > 0`): the
test-carrier computation of the general step value `-(f * log p)`. This
generalizes the `f = 1, p = 2` instance `realLineDilationLogWeight_half`. -/
theorem realLineDilationLogWeight_frobeniusStep (p : ℝ) (hp : 0 < p) (f : ℕ) :
    realLineDilationLogWeight (p ^ (-(f : ℝ))) = -((f : ℝ) * Real.log p) := by
  rw [realLineDilationLogWeight, abs_of_pos (Real.rpow_pos_of_pos hp (-(f : ℝ))),
    Real.log_rpow hp]
  ring

/-- The general step progression `mu-log((p ^ (-f)) ^ n . O) = -(f * n) * log p`
for integer labels `n`: the test-carrier form of `mu-log_k(m_k^n) =
-f * n * log p` ([AbsTopIII] Proposition 5.7, (i), (a), corpus :7932-7935) for
general `f` and positive real `p` (reduction: `p` and `f` enter only through
the real modulus `p ^ (-f)`). -/
theorem realLineLogShellLogVolume_frobeniusStep_pow (p : ℝ) (hp : 0 < p) (f : ℕ)
    (n : ℤ) :
    Real.log (normalizedRealLineVolume (((p ^ (-(f : ℝ))) ^ n) • unitInterval)).toReal =
      -((f : ℝ) * (n : ℝ)) * Real.log p := by
  have hbase : (0 : ℝ) < p ^ (-(f : ℝ)) := Real.rpow_pos_of_pos hp _
  rw [realLineLogShellLogVolume_dilation ((p ^ (-(f : ℝ))) ^ n),
    realLineDilationLogWeight, abs_zpow, abs_of_pos hbase, Real.log_zpow,
    Real.log_rpow hp]
  ring

/-- The consecutive-label increment in the general packaging: the step value
`-(f * log p)` is label-independent. -/
theorem realLineLogShellLogVolume_frobeniusStep_increment (p : ℝ) (hp : 0 < p)
    (f : ℕ) (n : ℤ) :
    Real.log (normalizedRealLineVolume (((p ^ (-(f : ℝ))) ^ (n + 1)) • unitInterval)).toReal -
      Real.log (normalizedRealLineVolume (((p ^ (-(f : ℝ))) ^ n) • unitInterval)).toReal =
        -((f : ℝ) * Real.log p) := by
  rw [realLineLogShellLogVolume_frobeniusStep_pow p hp f (n + 1),
    realLineLogShellLogVolume_frobeniusStep_pow p hp f n,
    Int.cast_add, Int.cast_one]
  ring

/-- The general step with a genuine prime `P : Nat.Prime P`: the faithful
packaging of `mu-log_k(m_k^n) = -f * n * log p` for prime `p`. The primality
hypothesis is present for fidelity to [AbsTopIII] Proposition 5.7, (i), (a)
and is not used by the real computation (reduction). -/
theorem realLineLogShellLogVolume_primeFrobeniusStep_increment (P : ℕ) (hP : Nat.Prime P)
    (f : ℕ) (n : ℤ) :
    Real.log (normalizedRealLineVolume ((((P : ℝ) ^ (-(f : ℝ))) ^ (n + 1)) • unitInterval)).toReal -
      Real.log (normalizedRealLineVolume ((((P : ℝ) ^ (-(f : ℝ))) ^ n) • unitInterval)).toReal =
        -((f : ℝ) * Real.log (P : ℝ)) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr hP.pos
  exact realLineLogShellLogVolume_frobeniusStep_increment (P : ℝ) hP0 f n

/-- Consistency instance: the general step at `p = 2`, `f = 1` recovers the
previous `f = 1, p = 2` instance (`realLineLogShellLogVolume_half_pow`),
extended here to integer labels. -/
theorem realLineLogShellLogVolume_primeStep_two (n : ℤ) :
    Real.log (normalizedRealLineVolume ((((2 : ℝ) ^ (-(1 : ℝ))) ^ n) • unitInterval)).toReal =
      -((n : ℝ) * Real.log 2) := by
  simpa using realLineLogShellLogVolume_frobeniusStep_pow 2 (by norm_num) 1 n

end

end LeanFormal.IUT.HaarTranslateModel.RealLine

namespace LeanFormal.IUT.Audit

/-- Audit record for the log-Frobenius compatibility fragment and the general
`-(f * n * log p)` step on the real-line test carrier (outsider survey
continuation: [AbsTopIII] Corollary 5.10, (ii); Proposition 5.7, (i), (a),
(c)). -/
def haarTranslateRealLineLogFrobeniusCompatibility : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-real-line-log-frobenius-compatibility"
    source :=
      "IUT III, Corollary 3.12, Step (xi); [AbsTopIII] Corollary 5.10, (ii) " ++
        "(Log-Frobenius Compatibility of Log-volumes, corpus :8594-8598), cf. " ++
        "Proposition 5.7, (i), (c) (:7952-7960); Proposition 5.7, (i), (a) " ++
        "(:7932-7935) -- test-carrier fragment"
    status := VerificationStatus.testCarrier
    note :=
      "Log-Frobenius compatibility minimal fragment on the real-line test " ++
        "carrier: the affine log-homotopy (realLineLogHomotopy, with " ++
        "continuity and affinity); interpolation of the measured log-volume " ++
        "along the family c ^ (n + s) (realLineLogShellLogVolume_homotopy_" ++
        "interpolation); consecutive-label compatibility with label-independent " ++
        "step weight dot-mu-log(c) (realLineLogShellLogVolume_logFrobenius_" ++
        "compatibility, realLineLogHomotopy_iterate). General -(f * n * log p) " ++
        "step: realLineDilationLogWeight_frobeniusStep, realLineLogShellLog" ++
        "Volume_frobeniusStep_pow/_increment, prime-packaged " ++
        "realLineLogShellLogVolume_primeFrobeniusStep_increment, consistency " ++
        "instance realLineLogShellLogVolume_primeStep_two. Reduced: labels " ++
        "modeled by reals with successor +1; the homotopy realized only as the " ++
        "affine log-domain segment; p and f enter only through the real " ++
        "modulus p ^ (-f) and log p; primality unused by the real computation. " ++
        "Additional data (not available): the shell-homotopy formalism, the " ++
        "label set L, radial/angular decomposition. The arithmetic log-volume, " ++
        "the literal carrier and the value-level boundary are untouched."
    dependsOn :=
      [ "IUT-III.corollary-3.12-haar-translate-real-line-log-compatibility",
        "IUT-III.corollary-3.12-haar-translate-real-line-consumer-wiring" ] }

end LeanFormal.IUT.Audit
