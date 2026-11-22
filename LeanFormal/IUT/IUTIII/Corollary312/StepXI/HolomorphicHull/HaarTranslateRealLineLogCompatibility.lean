import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateRealLineConsumerWiring
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
  # Multiplicative dilation and the signed log-volume on the real-line test carrier
  (outsider survey continuation: [AbsTopIII] Corollary 5.10, (ii))

  The remaining items of the raw-Haar vs normalized-log-volume gap (landing report,
  section 14) are continued here on the same test carrier, in the multiplicative form
  of [AbsTopIII] Proposition 5.7, (i), (b) (`M(k)`-multiplication and the weight
  `dot-mu`) and Corollary 5.10, (ii) (log-Frobenius compatibility of log-volumes):

  * `realLine_volume_dilation`: the additive Haar measure on the line rescales by the
    modulus under the dilation action `t |-> t * .` (one-dimensional `addHaar_smul`);
  * `realLineDilationLogWeight` = `log |t|`: the test-carrier weight `dot-mu-log` of
    `dot-mu(t) = mu(t . O)`, with additivity on products, vanishing on the
    modulus-one group, strict negativity on contracting dilations, and the
    power/zpow progression `dot-mu-log(c ^ n) = n . dot-mu-log(c)`;
  * `normalizedRealLineVolume_dilation_unitInterval`: `mu(t . O) = |t|` -- the exact
    `dot-mu(x) = mu(x . O)` shape on the unit log-shell `O = [-1, 1]`;
  * `normalizedRealLineVolume_dilation_decomposition`:
    `mu((t * u) . O) = |t| . mu(u . O)` -- the multiplicative decomposition
    `mu(x . A) = dot-mu(x) . mu(A)` of Proposition 5.7, (i), (b), for the log-shell
    family `A = u . O`; `normalizedRealLineVolume_dilation_units` is the invariance
    on units;
  * `realLineLogShellLogVolume_dilation` and `..._decomposition`: the signed layer
    `mu-log = log o mu` realizes `mu-log(t . O) = dot-mu-log(t)` and
    `mu-log(x . A) = mu-log(A) + dot-mu-log(x)`; `..._neg` gives the negative sign
    on contracting layers (the shape of `mu-log(m_k^n) = -f . n . log p`);
  * `realLineLogShellLogVolume_half_pow`: with the test step `c = 1/2` (f = 1, p = 2
    model), `mu-log(c ^ n . O) = -(n . log 2)` -- the exact progression shape with a
    concrete negative step value.

  Reductions (do not overclaim): the carrier is the additive line with dilation, not
  a local field with its multiplicative group; the field step value `-f . log p`
  (residue degree times log of the residue characteristic) is not derived here --
  only the progression shape is, with the free constant instantiated at `-log 2` as
  a test value; the normalization `mu(O) = 1` is the rescaled Lebesgue measure, not
  the arithmetic log-volume of [AbsTopIII]; the literal carrier and the value-level
  boundary are untouched.

  Evidence: `tmp/outsider-survey-iq-carrier-20261016/` logs and the landing report
  `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`, section 15.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.HaarTranslateModel.RealLine

noncomputable section

open MeasureTheory

-- The pointwise scalar-multiplication instance on sets (`Set.smulSet`) is a
-- scoped instance under `Pointwise` in Mathlib; it is needed for the dilation
-- action on sets (the same scope is opened in EqHaar.lean).
open scoped Pointwise

/-! ## 1. Haar rescaling under dilation -/

/-- Rescaling a set of the line by a factor `t` multiplies its Lebesgue (additive
Haar) measure by the modulus `|t|`; the one-dimensional case of `addHaar_smul`. -/
theorem realLine_volume_dilation (t : Real) (s : Set Real) :
    volume (t • s) = ENNReal.ofReal |t| * volume s := by
  have h := Measure.addHaar_smul volume t s
  rw [CommSemiring.finrank_self, pow_one] at h
  exact h

/-! ## 2. The multiplicative weight `dot-mu` and its log layer -/

/-- The test-carrier multiplicative weight `dot-mu(t) = |t|`: the modulus of the
dilation, i.e. `mu(t . O)` for the normalized measure (see
`normalizedRealLineVolume_dilation_unitInterval`). -/
def realLineDilationWeight (t : Real) : ENNReal := ENNReal.ofReal |t|

/-- The signed log weight `dot-mu-log(t) = log |t|`: the test-carrier form of
`dot-mu(x) := mu(x . O)` pushed through `log`, matching Proposition 5.7, (i), (b). -/
def realLineDilationLogWeight (t : Real) : Real := Real.log |t|

/-- Additivity of the log weight on products: the `dot-mu-log` face of the
multiplicativity of the weight. -/
theorem realLineDilationLogWeight_mul (t u : Real) (ht : t ≠ 0) (hu : u ≠ 0) :
    realLineDilationLogWeight (t * u) =
      realLineDilationLogWeight t + realLineDilationLogWeight u := by
  unfold realLineDilationLogWeight
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr ht) (abs_ne_zero.mpr hu)]

/-- The log weight vanishes on the modulus-one group: the test-carrier form of the
invariance `dot-mu(x) = 1` for `x` in the units `O^×` of Proposition 5.7, (i), (b). -/
theorem realLineDilationLogWeight_unit (t : Real) (ht : |t| = 1) :
    realLineDilationLogWeight t = 0 := by
  rw [realLineDilationLogWeight, ht, Real.log_one]

/-- The log weight is nonnegative on expanding dilations `|t| ≥ 1`. -/
theorem realLineDilationLogWeight_nonneg (t : Real) (ht : 1 ≤ |t|) :
    0 ≤ realLineDilationLogWeight t := by
  rw [realLineDilationLogWeight]
  exact Real.log_nonneg ht

/-- The log weight is strictly negative on contracting dilations `0 < |t| < 1`:
the sign shape of `mu-log(m_k^n) = -f . n . log p` for `n > 0`. -/
theorem realLineDilationLogWeight_neg (t : Real) (h0 : 0 < |t|) (h1 : |t| < 1) :
    realLineDilationLogWeight t < 0 := by
  rw [realLineDilationLogWeight]
  exact Real.log_neg h0 h1

/-- The progression law of the log weight on natural powers: the shape of
`mu-log(m_k^n) = n . mu-log(m_k)`. -/
theorem realLineDilationLogWeight_pow (c : Real) (n : ℕ) :
    realLineDilationLogWeight (c ^ n) = n * realLineDilationLogWeight c := by
  unfold realLineDilationLogWeight
  rw [abs_pow, Real.log_pow]

/-- The progression law of the log weight on integer powers (`m_k^n`, `n ∈ Z`). -/
theorem realLineDilationLogWeight_zpow (c : Real) (n : ℤ) :
    realLineDilationLogWeight (c ^ n) = n * realLineDilationLogWeight c := by
  unfold realLineDilationLogWeight
  rw [abs_zpow, Real.log_zpow]

/-- A concrete negative step value: `dot-mu-log(1/2) = -log 2` -- the test-carrier
instantiation of the `-f . log p` step at the model values `f = 1`, `p = 2`. -/
theorem realLineDilationLogWeight_half :
    realLineDilationLogWeight (1 / 2) = -Real.log 2 := by
  rw [realLineDilationLogWeight, abs_of_pos (by norm_num : (0 : Real) < 1 / 2),
    Real.log_div (by norm_num : (1 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0),
    Real.log_one]
  ring

/-! ## 3. Multiplicative equivariance of the normalized log-volume -/

/-- The normalized log-volume of the dilated unit log-shell: `mu(t . O) = |t|` --
the exact `dot-mu(t) = mu(t . O)` shape of Proposition 5.7, (i), (b). -/
theorem normalizedRealLineVolume_dilation_unitInterval (t : Real) :
    normalizedRealLineVolume (t • unitInterval) = realLineDilationWeight t := by
  rw [realLineDilationWeight, normalizedRealLineVolume, Measure.smul_apply,
    realLine_volume_dilation, realLine_unitInterval_volume,
    smul_eq_mul, mul_comm (ENNReal.ofReal |t|) (ENNReal.ofReal 2), ← mul_assoc,
    ENNReal.inv_mul_cancel
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : Real) < 2)))
      ENNReal.ofReal_ne_top,
    one_mul]

/-- **The multiplicative decomposition** `mu(x . A) = dot-mu(x) . mu(A)` of
Proposition 5.7, (i), (b), on the log-shell family `A = u . O`:
`mu((t * u) . O) = |t| . mu(u . O)`. -/
theorem normalizedRealLineVolume_dilation_decomposition (t u : Real) :
    normalizedRealLineVolume ((t * u) • unitInterval) =
      ENNReal.ofReal |t| * normalizedRealLineVolume (u • unitInterval) := by
  rw [normalizedRealLineVolume_dilation_unitInterval (t * u),
    normalizedRealLineVolume_dilation_unitInterval u]
  unfold realLineDilationWeight
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg t)]

/-- Invariance on units: the dilated log-shell `t . O` with `|t| = 1` carries
exactly the unit-region log-volume (Proposition 5.7, (i), (b), unit case). -/
theorem normalizedRealLineVolume_dilation_units (t : Real) (ht : |t| = 1) :
    normalizedRealLineVolume (t • unitInterval) =
      normalizedRealLineVolume unitInterval := by
  rw [normalizedRealLineVolume_dilation_unitInterval t, realLineDilationWeight, ht,
    normalizedRealLineVolume_unitInterval, ENNReal.ofReal_one]

/-! ## 4. The signed log-volume layer `mu-log` -/

/-- The signed log-volume of the dilated log-shell: `mu-log(t . O) = log |t|`. -/
theorem realLineLogShellLogVolume_dilation (t : Real) :
    Real.log (normalizedRealLineVolume (t • unitInterval)).toReal =
      realLineDilationLogWeight t := by
  rw [normalizedRealLineVolume_dilation_unitInterval t, realLineDilationWeight,
    ENNReal.toReal_ofReal (abs_nonneg t), realLineDilationLogWeight]

/-- **The log-layer decomposition** `mu-log(x . A) = mu-log(A) + dot-mu-log(x)` of
Proposition 5.7, (i), (b), on the log-shell family `A = u . O`. -/
theorem realLineLogShellLogVolume_dilation_decomposition (t u : Real) (ht : t ≠ 0)
    (hu : u ≠ 0) :
    Real.log (normalizedRealLineVolume ((t * u) • unitInterval)).toReal =
      Real.log (normalizedRealLineVolume (u • unitInterval)).toReal +
        realLineDilationLogWeight t := by
  rw [realLineLogShellLogVolume_dilation (t * u), realLineLogShellLogVolume_dilation u,
    realLineDilationLogWeight_mul t u ht hu, add_comm]

/-- The signed log-volume vanishes on the units: `x ∈ O^×` does not move `mu-log`. -/
theorem realLineLogShellLogVolume_units (t : Real) (ht : |t| = 1) :
    Real.log (normalizedRealLineVolume (t • unitInterval)).toReal = 0 := by
  rw [realLineLogShellLogVolume_dilation t, realLineDilationLogWeight_unit t ht]

/-- The signed log-volume is strictly negative on contracting dilations:
`mu-log(t . O) < 0` for `0 < |t| < 1`. -/
theorem realLineLogShellLogVolume_neg (t : Real) (h0 : 0 < |t|) (h1 : |t| < 1) :
    Real.log (normalizedRealLineVolume (t • unitInterval)).toReal < 0 := by
  rw [realLineLogShellLogVolume_dilation t]
  exact realLineDilationLogWeight_neg t h0 h1

/-- The progression law `mu-log(c ^ n . O) = n . dot-mu-log(c)`: the exact shape of
`mu-log(m_k^n) = n . mu-log(m_k)`. -/
theorem realLineLogShellLogVolume_pow (c : Real) (n : ℕ) :
    Real.log (normalizedRealLineVolume ((c ^ n) • unitInterval)).toReal =
      n * realLineDilationLogWeight c := by
  rw [realLineLogShellLogVolume_dilation (c ^ n), realLineDilationLogWeight_pow c n]

/-- The concrete progression: with the test step `c = 1/2` (f = 1, p = 2 model),
`mu-log(c ^ n . O) = -(n . log 2)` -- the shape of `-f . n . log p`. -/
theorem realLineLogShellLogVolume_half_pow (n : ℕ) :
    Real.log (normalizedRealLineVolume (((1 / 2 : Real) ^ n) • unitInterval)).toReal =
      -(n * Real.log 2) := by
  rw [realLineLogShellLogVolume_pow (1 / 2) n, realLineDilationLogWeight_half]
  ring

end

end LeanFormal.IUT.HaarTranslateModel.RealLine

namespace LeanFormal.IUT.Audit

/-- Audit record for the multiplicative dilation and signed log-volume layer on the
real-line test carrier (outsider survey continuation: [AbsTopIII] Corollary 5.10,
(ii); Proposition 5.7, (i), (b)). -/
def haarTranslateRealLineLogCompatibility : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-real-line-log-compatibility"
    source :=
      "IUT III, Corollary 3.12, Step (xi); [AbsTopIII] Proposition 5.7, (i), (b) " ++
        "(multiplicative decomposition mu(x . A) = dot-mu(x) . mu(A)); Corollary " ++
        "5.10, (ii) (log-Frobenius compatibility of log-volumes) -- test-carrier form"
    status := VerificationStatus.testCarrier
    note :=
      "Multiplicative dilation layer on the real-line test carrier: the additive " ++
        "Haar measure rescales by the modulus (realLine_volume_dilation, " ++
        "addHaar_smul); the weight dot-mu(t) = |t| = mu(t . O) on the normalized " ++
        "unit log-shell (normalizedRealLineVolume_dilation_unitInterval); the " ++
        "multiplicative decomposition mu((t * u) . O) = |t| . mu(u . O) " ++
        "(normalizedRealLineVolume_dilation_decomposition); units invariance; the " ++
        "signed layer mu-log = log o mu realizing mu-log(x . A) = mu-log(A) + " ++
        "dot-mu-log(x) with its sign behavior; the progression shape " ++
        "dot-mu-log(c ^ n) = n . dot-mu-log(c) with test step -log 2 " ++
        "(realLineLogShellLogVolume_half_pow). Reductions: additive line with " ++
        "dilation, not a local field's multiplicative group; the field constant " ++
        "-f . log p is not derived (only the progression shape with a test value); " ++
        "mu(O) = 1 is the rescaled Lebesgue measure, not the arithmetic " ++
        "log-volume; the literal carrier and the value-level boundary are untouched."
    dependsOn :=
      [ "IUT-III.corollary-3.12-haar-translate-real-line-consumer-wiring",
        "IUT-III.corollary-3.12-haar-translate-real-line-instance" ] }

end LeanFormal.IUT.Audit
