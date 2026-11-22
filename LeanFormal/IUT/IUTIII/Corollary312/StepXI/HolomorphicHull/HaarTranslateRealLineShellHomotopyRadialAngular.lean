import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateRealLineLogFrobeniusCompatibility

/-!
  # Shell-homotopy formal system and radial/angular direction on the real-line
  test carrier (outsider survey continuation: [AbsTopIII] Corollary 5.10, (ii))

  The remaining two ingredients of the Corollary 5.10, (ii) minimal fragment
  (landing report, section 17) are addressed here.

  ## Shell-homotopy formal system (source quotes, OCR spacing normalized)

  * [AbsTopIII] corpus :8561-8566:

      "We shall refer to the natural transformation 'iota-plus_{v,eps}' of
      Corollary 5.5, (iii), as a shell-homotopy [at v] if eps is a shell-arrow
      [cf. Definition 5.4, (iii), (v)]; we shall refer to 'iota-plus_{v,eps}'
      as a log-homotopy [at v] if the initial vertex of eps is a post-log
      vertex."

  * Minimal fragment: `RealLineLogShellHomotopySystem c` packages the shape of
    such a homotopy on the test carrier -- an integer-labeled family of dilated
    log-shells (`shell`, with successor), the measured log-volume at each label
    (`logVolumeAt`), the path-valued homotopy matching the label segment
    (`homotopyValue`, with endpoint laws at 0 and 1), the interpolation law of
    Proposition 5.7, (i), (c), and the (ii)-compatibility law (the
    consecutive-label increment equals the step weight `dot-mu-log(c)`).
    The instance `realLineLogShellHomotopySystem` is built entirely from the
    proved lemmas of sections 15 and 17 (every field discharged; no additional
    data); its laws are re-exported as
    `realLineLogShellHomotopySystem_compatibility` and
    `realLineLogShellHomotopySystem_rpow_compatibility`.

  ## Radial/angular direction (source quotes, OCR spacing normalized)

  * [AbsTopIII] Proposition 5.7, (ii) (corpus :7962, :7986-8005):

      "we have a natural decomposition k^times = O^times_k x R_{>0}, where
      O^times_k = S^1; ... (2) normalization, i.e., mu_k(O_k) = 1
      (respectively, breve-mu_k(O^times_k) = 2 pi). We shall refer to mu_k(-)
      (respectively, breve-mu_k(-)) as the radial volume (respectively, angular
      volume) on k. Also, we shall write mu-log_k(-) = log(mu_k(-))
      (respectively, breve-mu-log_k(-) = log(breve-mu_k(-))) and refer to
      mu-log_k(-) (respectively, breve-mu-log_k(-)) as the radial log-volume
      (respectively, angular log-volume) on k."

  * [AbsTopIII] corpus :8190-8194 (normalization identity):

      "mu-log(G)(I(G)) = breve-mu-log(G)(O^times_{k-sim}(G)) - log(2) * F(G)
      / 2 pi = log(pi) * F(G) / 2 pi"

      determined by composing the maps mu-log_{k-sim(G)},
      breve-mu-log_{k-sim(G)} of Proposition 5.7, (ii), (a), with the
      isomorphism R -> R-arc(G) given by 2 pi |-> F(G).

  * Minimal fragment: `realLineAngularComponent` (the sign in {+1, -1}) and
    `realLineRadialComponent` (absolute value); the polar factorization; the
    invariance of the angular component under positive dilations and its
    label-independence along the shells; the radial consecutive-label increment
    (`realLineRadialLogVolume_shell_increment`); the angular normalization
    constant `2 * pi`; the normalization identity at the test value
    `F(G) = 2 * pi` (`realLineRadialAngularNormalization_identity`); and the
    packet-layer zero point `mu-log(O) = 0`
    (`realLineLogShellLogVolume_unit_zero`, G5 two-layer accounting).

  ## Annotations

  * proved: every theorem below, and every field of the instance;
  * reduced: the natural transformation `iota-plus_{v,eps}` and its shell-arrow
    are modeled by an integer-labeled family with successor and an affine
    log-domain segment; the angular group `O^times_k = S^1` is modeled by
    {+1, -1} (the real-line value group); "computed at label / label + 1" are
    integer labels with real parameter values 0 / 1; the radial/angular volumes
    are realized through the normalized log-shell volumes only; the
    normalization constant `F(G)` is set to `2 * pi`;
  * additional data (not available on this carrier): the ambient categories
    N^plus_v / N^{plus-dagger}_v, the capsule/LGP-monoid formalism, and the
    literal arithmetic log-volume.

  Evidence: `tmp/outsider-survey-iq-carrier-20261016/` logs and the landing
  report `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`,
  section 18.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.HaarTranslateModel.RealLine

noncomputable section

open MeasureTheory
open scoped Pointwise

/-! ## 1. Minimal fragment of the shell-homotopy formal system -/

/-- Minimal fragment of the shell-homotopy formal system of [AbsTopIII]
(corpus :8561-8566): an integer-labeled family of dilated log-shells with a
path-valued homotopy between consecutive labels carrying the (ii)-compatibility
law (consecutive-label log-volume increment = step weight `dot-mu-log(c)`).
Reduction: the natural transformation `iota-plus_{v,eps}` of Corollary 5.5,
(iii) is modeled by this structure; the homotopy path is the affine log-domain
segment `realLineLogHomotopy`. -/
structure RealLineLogShellHomotopySystem (c : ℝ) where
  pos : 0 < c
  shell : ℤ → Set ℝ
  shell_eq : ∀ n, shell n = (c ^ n) • unitInterval
  logVolumeAt : ℤ → ℝ
  logVolumeAt_eq : ∀ n,
    logVolumeAt n = Real.log (normalizedRealLineVolume (shell n)).toReal
  homotopyValue : ℝ → ℝ → ℝ
  homotopyValue_eq : ∀ n s, homotopyValue n s = realLineLogHomotopy c n s
  endpoint_zero : ∀ n : ℤ, homotopyValue (n : ℝ) 0 = logVolumeAt n
  endpoint_one : ∀ n : ℤ, homotopyValue (n : ℝ) 1 = logVolumeAt (n + 1)
  interpolation : ∀ (n s : ℝ),
    Real.log (normalizedRealLineVolume ((c ^ (n + s)) • unitInterval)).toReal =
      homotopyValue n s
  compatibility : ∀ n : ℤ,
    logVolumeAt (n + 1) - logVolumeAt n = realLineDilationLogWeight c

/-- The affine log-scale system instantiating the shell-homotopy formal
system: labeled shells `c ^ n . O`, log-volume `n * log c` at the label `n`,
and the homotopy value function `realLineLogHomotopy c`. Every field is
discharged by the proved lemmas of sections 15 and 17. -/
def realLineLogShellHomotopySystem (c : ℝ) (hc : 0 < c) :
    RealLineLogShellHomotopySystem c where
  pos := hc
  shell := fun n => (c ^ n) • unitInterval
  shell_eq := fun _ => rfl
  logVolumeAt := fun n => (n : ℝ) * Real.log c
  logVolumeAt_eq := by
    intro n
    show (n : ℝ) * Real.log c =
      Real.log (normalizedRealLineVolume ((c ^ n) • unitInterval)).toReal
    rw [realLineLogShellLogVolume_dilation (c ^ n), realLineDilationLogWeight_zpow,
      realLineDilationLogWeight, abs_of_pos hc]
  homotopyValue := realLineLogHomotopy c
  homotopyValue_eq := fun _ _ => rfl
  endpoint_zero := by
    intro n
    show realLineLogHomotopy c (n : ℝ) 0 = (n : ℝ) * Real.log c
    rw [realLineLogHomotopy, abs_of_pos hc]
    ring
  endpoint_one := by
    intro n
    show realLineLogHomotopy c (n : ℝ) 1 = (↑(n + 1) : ℝ) * Real.log c
    rw [realLineLogHomotopy, abs_of_pos hc, Int.cast_add, Int.cast_one]
  interpolation := fun n s =>
    realLineLogShellLogVolume_homotopy_interpolation c hc n s
  compatibility := by
    intro n
    show (↑(n + 1) : ℝ) * Real.log c - (n : ℝ) * Real.log c =
      realLineDilationLogWeight c
    rw [Int.cast_add, Int.cast_one, realLineDilationLogWeight, abs_of_pos hc]
    ring

/-- The instantiated log-volume at the label `n`. -/
theorem realLineLogShellHomotopySystem_logVolumeAt (c : ℝ) (hc : 0 < c) (n : ℤ) :
    (realLineLogShellHomotopySystem c hc).logVolumeAt n = (n : ℝ) * Real.log c :=
  rfl

/-- The (ii)-compatibility law instantiated by the affine log-scale system. -/
theorem realLineLogShellHomotopySystem_compatibility (c : ℝ) (hc : 0 < c)
    (n : ℤ) :
    (realLineLogShellHomotopySystem c hc).logVolumeAt (n + 1) -
      (realLineLogShellHomotopySystem c hc).logVolumeAt n =
        realLineDilationLogWeight c :=
  (realLineLogShellHomotopySystem c hc).compatibility n

/-- The same law in the real-parameter (rpow) family of section 17. -/
theorem realLineLogShellHomotopySystem_rpow_compatibility (c : ℝ) (hc : 0 < c)
    (n : ℝ) :
    Real.log (normalizedRealLineVolume ((c ^ (n + 1)) • unitInterval)).toReal -
      Real.log (normalizedRealLineVolume ((c ^ n) • unitInterval)).toReal =
        realLineDilationLogWeight c :=
  realLineLogShellLogVolume_logFrobenius_compatibility c hc n

/-! ## 2. Radial/angular direction: the minimal fragment -/

/-- The angular component of a real number: the sign in {+1, -1} -- the
test-carrier model of the angular projection `k^times -> O^times_k` of
[AbsTopIII] Proposition 5.7, (ii). Reduction: the paper displays
`O^times_k = S^1`; on the real line the value group is two-valued, so only
{+1, -1} is modeled. -/
def realLineAngularComponent (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- The radial component of a real number: the absolute value -- the
test-carrier model of the radial projection `k^times -> R_{>0}` of
[AbsTopIII] Proposition 5.7, (ii). -/
def realLineRadialComponent (x : ℝ) : ℝ := |x|

/-- The angular component squares to one: its values lie in {+1, -1}. -/
theorem realLineAngularComponent_sq (x : ℝ) :
    realLineAngularComponent x ^ 2 = 1 := by
  unfold realLineAngularComponent
  split <;> norm_num

/-- Positive dilations act on the radial factor only: the angular component is
invariant under scaling by `t > 0` -- the angular face of the log-homotopy
(the angular computation does not move along positive dilations). -/
theorem realLineAngularComponent_pos_scaling (t x : ℝ) (ht : 0 < t) :
    realLineAngularComponent (t * x) = realLineAngularComponent x := by
  unfold realLineAngularComponent
  by_cases h : 0 ≤ x
  · rw [if_pos (mul_nonneg (le_of_lt ht) h), if_pos h]
  · rw [if_neg (not_le.mpr (mul_neg_of_pos_of_neg ht (not_le.mp h))), if_neg h]

/-- The radial component rescales by `t` under scaling by `t > 0`. -/
theorem realLineRadialComponent_pos_scaling (t x : ℝ) (ht : 0 < t) :
    realLineRadialComponent (t * x) = t * realLineRadialComponent x := by
  unfold realLineRadialComponent
  rw [abs_mul, abs_of_pos ht]

/-- Polar factorization on the test carrier: `x = angular x * radial x` --
the two-valued form of the decomposition `k^times = O^times_k x R_{>0}` of
[AbsTopIII] Proposition 5.7, (ii). -/
theorem realLinePolarFactorization (x : ℝ) :
    realLineAngularComponent x * realLineRadialComponent x = x := by
  unfold realLineAngularComponent realLineRadialComponent
  by_cases h : 0 ≤ x
  · rw [if_pos h, abs_of_nonneg h, one_mul]
  · rw [if_neg h, abs_of_neg (not_le.mp h)]
    ring

/-- Angular label-independence along the shells: the angular component of
`c ^ n * x` is independent of the label `n` (`c > 0`) -- the angular face of
Corollary 5.10, (ii): the angular computation does not move along the
log-homotopy. -/
theorem realLineAngularComponent_shell_label_independent (c : ℝ) (hc : 0 < c)
    (n : ℤ) (x : ℝ) :
    realLineAngularComponent ((c ^ n) * x) = realLineAngularComponent x :=
  realLineAngularComponent_pos_scaling (c ^ n) x (zpow_pos hc n)

/-- The radial face of Corollary 5.10, (ii) on the shells: the consecutive
label increment of the (radial) log-volume is the step weight
`dot-mu-log(c)`, uniformly in the label. -/
theorem realLineRadialLogVolume_shell_increment (c : ℝ) (hc : 0 < c) (n : ℤ) :
    Real.log (normalizedRealLineVolume ((c ^ (n + 1)) • unitInterval)).toReal -
      Real.log (normalizedRealLineVolume ((c ^ n) • unitInterval)).toReal =
        realLineDilationLogWeight c := by
  rw [realLineLogShellLogVolume_dilation (c ^ (n + 1)),
    realLineLogShellLogVolume_dilation (c ^ n), realLineDilationLogWeight_zpow,
    realLineDilationLogWeight_zpow, realLineDilationLogWeight, abs_of_pos hc,
    Int.cast_add, Int.cast_one]
  ring

/-- The angular normalization constant of the test carrier: `2 * pi`, the
value `breve-mu_k(O^times_k) = 2 pi` of [AbsTopIII] Proposition 5.7, (ii). -/
def realLineAngularNormalization : ℝ := 2 * Real.pi

/-- The angular normalization is positive. -/
theorem realLineAngularNormalization_pos : 0 < realLineAngularNormalization := by
  unfold realLineAngularNormalization
  positivity

/-- The angular log-volume of the unit circle splits additively:
`log (2 * pi) = log 2 + log pi` -- the composition `breve-mu-log = log o
breve-mu` at the normalization value `breve-mu(O^times_k) = 2 * pi`. -/
theorem realLineAngularLogVolume_unitCircle :
    Real.log realLineAngularNormalization = Real.log 2 + Real.log Real.pi := by
  rw [realLineAngularNormalization,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]

/-- The [AbsTopIII] normalization identity (corpus :8190-8194) at the test
value `F(G) = 2 * pi`: with `F(G) / 2 pi = 1`, the quoted formula
`mu-log(G)(I(G)) = breve-mu-log(G)(O^times) - log(2) * F(G) / 2 pi` reads
`log pi = log (2 * pi) - log 2`. -/
theorem realLineRadialAngularNormalization_identity :
    Real.log Real.pi = Real.log (2 * Real.pi) - Real.log 2 := by
  rw [← Real.log_div
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- The packet-layer zero point of the log-volume normalization (the
`mu-log(O) = 0` normalization of [AbsTopIII] Proposition 3.9, (i); G5
two-layer accounting): the unit log-shell carries log-volume zero. -/
theorem realLineLogShellLogVolume_unit_zero :
    Real.log (normalizedRealLineVolume unitInterval).toReal = 0 := by
  rw [normalizedRealLineVolume_unitInterval, ENNReal.toReal_one, Real.log_one]

end

end LeanFormal.IUT.HaarTranslateModel.RealLine

namespace LeanFormal.IUT.Audit

/-- Audit record for the shell-homotopy formal-system fragment and the
radial/angular direction on the real-line test carrier (outsider survey
continuation: [AbsTopIII] Corollary 5.10, (ii); shell-homotopy definition
corpus :8561-8566; radial/angular volumes Proposition 5.7, (ii), corpus
:7962, :7986-8005; normalization identity corpus :8190-8194). -/
def haarTranslateRealLineShellHomotopyRadialAngular : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-real-line-shell-homotopy-radial-angular"
    source :=
      "IUT III, Corollary 3.12, Step (xi); [AbsTopIII] Corollary 5.10, (ii) " ++
        "(Log-Frobenius Compatibility of Log-volumes, corpus :8594-8598); " ++
        "shell-homotopy / log-homotopy definition (corpus :8561-8566); " ++
        "Proposition 5.7, (ii), radial and angular log-volumes (corpus :7962, " ++
        ":7986-8005); normalization identity (corpus :8190-8194) -- " ++
        "test-carrier fragments"
    status := VerificationStatus.testCarrier
    note :=
      "Shell-homotopy formal-system minimal fragment: the structure " ++
        "RealLineLogShellHomotopySystem (integer-labeled shells with successor, " ++
        "log-volume at a label, path-valued homotopy with endpoint laws, " ++
        "interpolation, consecutive-label compatibility), instantiated by " ++
        "realLineLogShellHomotopySystem with every field discharged by the " ++
        "sections 15/17 lemmas (realLineLogShellHomotopySystem_logVolumeAt, " ++
        "realLineLogShellHomotopySystem_compatibility, " ++
        "realLineLogShellHomotopySystem_rpow_compatibility). Radial/angular " ++
        "minimal fragment: realLineAngularComponent / realLineRadialComponent " ++
        "with realLinePolarFactorization; angular invariance under positive " ++
        "dilations (realLineAngularComponent_pos_scaling) and label-independence " ++
        "along the shells (realLineAngularComponent_shell_label_independent); " ++
        "the radial consecutive-label increment " ++
        "realLineRadialLogVolume_shell_increment; the angular normalization " ++
        "constant 2 * pi with realLineAngularNormalization_pos and " ++
        "realLineAngularLogVolume_unitCircle; the normalization identity " ++
        "realLineRadialAngularNormalization_identity; and the packet-layer zero " ++
        "point realLineLogShellLogVolume_unit_zero. Reduced: the natural " ++
        "transformation iota-plus_{v,eps} is modeled by the structure; integer " ++
        "labels; angular group {+1, -1} instead of S^1; F(G) set to 2 * pi. " ++
        "Additional data (not available): N^plus_v / N^{plus-dagger}_v ambient " ++
        "categories, capsule/LGP-monoid formalism, literal arithmetic " ++
        "log-volume."
    dependsOn :=
      [ "IUT-III.corollary-3.12-haar-translate-real-line-log-frobenius-compatibility" ] }

end LeanFormal.IUT.Audit
