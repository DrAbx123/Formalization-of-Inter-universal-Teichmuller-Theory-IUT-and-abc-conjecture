import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual
import tmp.sheaf.xif.paper.S764ThetaHullMinVsAverageActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # W4: quadratic Gauss / second-moment identities versus the least lambda-O hull log

Task W4 asked whether the exact finite Fourier/Gauss identities of Task L
(mu_{2l}-orbit average zero, quadratic Gauss sums, and the label second moment
(l+1)/24) can be used to identify the normalized Haar log of the paper's
least lambda-O holomorphic hull, or to prove that the l*-label average equals
that hull log.

This file records the exact no-go in the actual paper objects.

Positive side: the least lambda-O hull is paperLeastLambdaOHull (S793), and
once the pure fractional scaling datum is supplied its normalized log is the
hull-extremum formula paperQPilotLogLeast (S799); see
paperLeastLambdaOHullLog_eq_leastFormula_of_data.

Negative side:
* the l*-label average of the paper exponents is exactly the second moment
  coefficient (l+1)/24 (w4ThetaLabelAverage_eq);
* every probability average of the label exponents is at least the hull
  minimum 1/(2l), and is strictly larger as soon as positive mass is put on
  a nonzero label (w4HullMin_lt_weightedAverage_of_pos);
* consequently the l* average log is strictly smaller than the least-hull
  log whenever the order and log p are positive
  (paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data).

The mu_{2l}-orbit identity is formalized on the actual finite root stack:
for the primitive 2l-th root stackMuRoot in the root extension ambient field,
the orbit sum of every nonzero paper label vanishes exactly
(stackMuRoot_orbitAverage_eq_zero).  It is a phase/annihilation identity, not
a positive normalization: it cannot equal the (strictly negative) hull log.

No inequality is assumed; no paper target is changed.  The file does not import
S704PaperThetaLogVolumeFormulaActual because that file's current source does
not compile against the present tree; w4ThetaExponent is the same formula
j^2/(2l) used there.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.W4GaussSecondMomentNoGoActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.S764ThetaHullMinVsAverageActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u

/-! ## 1. The exact paper label arithmetic -/

theorem sum_range_sq_succ (n : Nat) :
    (∑ i ∈ Finset.range n, ((i + 1 : Real)^2)) =
      (n : Real) * (n + 1) * (2*n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem lStar_two_mul_add_one (l : PrimeGeFive) :
    2 * lStar l.value + 1 = l.value := by
  unfold lStar
  have hodd : l.value % 2 = 1 := by
    rcases l.odd with ⟨k, hk⟩
    omega
  have h := Nat.two_mul_odd_div_two hodd
  omega

/-- Second-moment sum of the paper label exponents before dividing by 2l. -/
theorem sum_sq_paperThetaLabel (l : PrimeGeFive) :
    (∑ i : PaperThetaLabel l, ((i.1 + 1 : Real)^2)) =
      (l.value : Real) * ((l.value : Real)^2 - 1) / 24 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => ((i + 1 : Real)^2))]
  rw [sum_range_sq_succ]
  have h2 : (2 * (lStar l.value : Real) + 1) = (l.value : Real) := by
    exact_mod_cast lStar_two_mul_add_one l
  have hn : (lStar l.value : Real) = ((l.value : Real) - 1) / 2 := by linarith
  rw [hn]
  ring

/-- The paper theta exponent j^2/(2l) (S704 formula, kept local). -/
def w4ThetaExponent (l : PrimeGeFive) (j : PaperThetaLabel l) : Real :=
  ((j.1 + 1 : Real)^2) / (2 * (l.value : Real))

/-- The hull-extremum coefficient 1/(2l) (S764/S793). -/
noncomputable def w4HullMinCoefficient (l : PrimeGeFive) : Real :=
  1 / (2 * (l.value : Real))

/-- The second-moment/average coefficient (l+1)/24 (S694/S764). -/
noncomputable def w4AverageCoefficient (l : PrimeGeFive) : Real :=
  ((l.value : Real) + 1) / 24

theorem w4HullMinCoefficient_eq (l : PrimeGeFive) :
    w4HullMinCoefficient l = paperThetaHullMinCoefficient (l := l) := rfl

theorem w4AverageCoefficient_eq (l : PrimeGeFive) :
    w4AverageCoefficient l = paperThetaAverageCoefficient (l := l) := rfl

/-- Exact second-moment identity: the l* average of j^2/(2l) is (l+1)/24. -/
theorem w4ThetaLabelAverage_eq (l : PrimeGeFive) :
    paperThetaLabelAverage (l := l) (fun j => w4ThetaExponent l j) =
      w4AverageCoefficient l := by
  unfold paperThetaLabelAverage w4AverageCoefficient w4ThetaExponent
    paperThetaLabelWeight
  change (lStar l.value : Real)⁻¹ *
      (∑ i : PaperThetaLabel l, ((i.1 + 1 : Real)^2) / (2 * (l.value : Real))) =
    ((l.value : Real) + 1) / 24
  rw [← Finset.sum_div]
  rw [sum_sq_paperThetaLabel]
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  have hls : (lStar l.value : Real) ≠ 0 := by
    have h : 0 < lStar l.value := by
      have h5 := l.ge_five
      unfold lStar
      omega
    exact_mod_cast Nat.ne_of_gt h
  have h2 : (2 * (lStar l.value : Real) + 1) = (l.value : Real) := by
    exact_mod_cast lStar_two_mul_add_one l
  field_simp [hl, hls]
  nlinarith

/-- The second-moment coefficient is strictly larger than the hull minimum. -/
theorem w4HullMin_lt_average (l : PrimeGeFive) :
    w4HullMinCoefficient l < w4AverageCoefficient l := by
  rw [w4HullMinCoefficient_eq, w4AverageCoefficient_eq]
  exact paperThetaHullMinCoefficient_lt_averageCoefficient (l := l)

/-! ## 2. No weighted label average can equal the hull minimum

This is the general form of the obstruction: the hull log is an extremum of
the exponent vector, while Gauss sums / moments are weighted averages of the
same exponents.  A probability weight can equal the minimum only if all mass
is concentrated on the minimizing label j = 1. -/

theorem w4HullMin_le_exponent (l : PrimeGeFive) (i : PaperThetaLabel l) :
    w4HullMinCoefficient l ≤ w4ThetaExponent l i := by
  unfold w4HullMinCoefficient w4ThetaExponent
  have hsq : (1 : Real) ≤ ((i.1 + 1 : Real)^2) := by
    have hi : (1 : Real) ≤ (i.1 + 1 : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
    nlinarith [sq_nonneg ((i.1 : Real))]
  have hlpos : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have hl : (0 : Real) < 2 * (l.value : Real) := by positivity
  exact div_le_div_of_nonneg_right hsq hl.le

theorem w4HullMin_le_weightedAverage (l : PrimeGeFive)
    (w : PaperThetaLabel l → Real) (hw : ∀ i, 0 ≤ w i)
    (hsum : (∑ i, w i) = 1) :
    w4HullMinCoefficient l ≤ ∑ i, w i * w4ThetaExponent l i := by
  calc
    w4HullMinCoefficient l = w4HullMinCoefficient l * (∑ i, w i) := by
      rw [hsum, mul_one]
    _ = ∑ i, w4HullMinCoefficient l * w i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, w i * w4ThetaExponent l i := by
      apply Finset.sum_le_sum
      intro i _
      calc
        w4HullMinCoefficient l * w i = w i * w4HullMinCoefficient l := by ring
        _ ≤ w i * w4ThetaExponent l i :=
          mul_le_mul_of_nonneg_left (w4HullMin_le_exponent l i) (hw i)

/-- At a nonzero label the exponent is strictly above the hull minimum. -/
theorem w4HullMin_lt_exponent_of_ne_zero (l : PrimeGeFive)
    (i : PaperThetaLabel l) (hi : i.1 ≠ 0) :
    w4HullMinCoefficient l < w4ThetaExponent l i := by
  unfold w4HullMinCoefficient w4ThetaExponent
  have hsq : (1 : Real) < ((i.1 + 1 : Real)^2) := by
    have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi
    have hi2 : (2 : Real) ≤ (i.1 + 1 : Real) := by
      exact_mod_cast Nat.succ_le_succ (Nat.succ_le_of_lt hipos)
    nlinarith [sq_nonneg ((i.1 : Real))]
  have hlpos : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have hl : (0 : Real) < 2 * (l.value : Real) := by positivity
  exact div_lt_div_of_pos_right hsq hl

/-- Any probability average with positive mass on a nonzero label is strictly
above the hull minimum.  This is the exact sense in which a character sum or a
second moment cannot see the extremal coefficient. -/
theorem w4HullMin_lt_weightedAverage_of_pos (l : PrimeGeFive)
    (w : PaperThetaLabel l → Real) (hw : ∀ i, 0 ≤ w i)
    (hsum : (∑ i, w i) = 1) (i0 : PaperThetaLabel l)
    (hi0 : i0.1 ≠ 0) (hpos : 0 < w i0) :
    w4HullMinCoefficient l < ∑ i, w i * w4ThetaExponent l i := by
  have hstrict := w4HullMin_lt_exponent_of_ne_zero l i0 hi0
  have hd_nonneg : ∀ i, 0 ≤ w i * (w4ThetaExponent l i - w4HullMinCoefficient l) := by
    intro i
    exact mul_nonneg (hw i) (sub_nonneg.mpr (w4HullMin_le_exponent l i))
  have hd_i0 : 0 < w i0 * (w4ThetaExponent l i0 - w4HullMinCoefficient l) :=
    mul_pos hpos (sub_pos.mpr hstrict)
  have hsingle : w i0 * (w4ThetaExponent l i0 - w4HullMinCoefficient l) ≤
      ∑ i, w i * (w4ThetaExponent l i - w4HullMinCoefficient l) :=
    Finset.single_le_sum (fun i _ => hd_nonneg i) (Finset.mem_univ i0)
  have hsumpos : 0 < ∑ i, w i * (w4ThetaExponent l i - w4HullMinCoefficient l) :=
    lt_of_lt_of_le hd_i0 hsingle
  have hm : (∑ i, w i * w4HullMinCoefficient l) = w4HullMinCoefficient l := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hdecomp :
      (∑ i, w i * w4ThetaExponent l i) - w4HullMinCoefficient l =
        ∑ i, w i * (w4ThetaExponent l i - w4HullMinCoefficient l) := by
    conv_lhs => rw [← hm]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

/-! ## 3. The mu_{2l}-orbit annihilation on the actual finite root stack

The orbit values are (zeta^m q)^(j^2).  Since 2l does not divide j^2 for
0 < j < l, the geometric sum over the orbit vanishes exactly. -/

theorem orbit_sum_eq_zero {K : Type*} [Field K] (ζ q : K) {n j : Nat}
    (hζn : ζ ^ n = 1) (hζj : ζ ^ (j^2) ≠ 1) :
    (∑ m ∈ Finset.range n, (ζ ^ m * q) ^ (j^2)) = 0 := by
  have hxn : (ζ ^ (j^2)) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζn, one_pow]
  have hsum : (∑ m ∈ Finset.range n, (ζ ^ (j^2)) ^ m) = 0 := by
    rw [geom_sum_eq hζj n, hxn, sub_self, zero_div]
  calc
    (∑ m ∈ Finset.range n, (ζ ^ m * q) ^ (j^2))
        = ∑ m ∈ Finset.range n, ((ζ ^ (j^2)) ^ m * q ^ (j^2)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m (j^2)]
    _ = (∑ m ∈ Finset.range n, (ζ ^ (j^2)) ^ m) * q ^ (j^2) := by
          rw [Finset.sum_mul]
    _ = 0 := by rw [hsum, zero_mul]

theorem twoL_not_dvd_sq {l j : Nat} (hl : Nat.Prime l)
    (hj : 0 < j) (hjl : j < l) : ¬ (2 * l) ∣ j ^ 2 := by
  intro h
  have h2l : l ∣ 2 * l := ⟨2, by ring⟩
  have hldvd : l ∣ j ^ 2 := dvd_trans h2l h
  have hlj : l ∣ j := hl.dvd_of_dvd_pow hldvd
  have hle : l ≤ j := Nat.le_of_dvd hj hlj
  omega

variable {l : PrimeGeFive}

/-- The chosen 2l-th root of the finite root-stack extension is primitive. -/
theorem stackMuRoot_isPrimitive (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T)) :
    IsPrimitiveRoot
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b)) (2 * l.value) := by
  unfold stackMuRoot
  exact Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot
    (rootNormedAmbient T b) (2 * l.value))

/-- Exact mu_{2l}-orbit annihilation for every nonzero paper label. -/
theorem stackMuRoot_orbitAverage_eq_zero
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T))
    (q : rootNormedAmbient T b)
    {j : Nat} (hj : 0 < j) (hjl : j < l.value) :
    (∑ m ∈ Finset.range (2 * l.value),
      ((((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
          rootNormedAmbient T b) ^ m) * q) ^ (j ^ 2)) = 0 := by
  apply orbit_sum_eq_zero
  · exact (stackMuRoot_isPrimitive (l := l) T b).pow_eq_one
  · intro h
    exact twoL_not_dvd_sq l.prime hj hjl
      ((stackMuRoot_isPrimitive (l := l) T b).dvd_of_pow_eq_one (j ^ 2) h)

/-! ## 4. The actual l* average of the root theta magnitudes

The paper theta value at a positive label is the root magnitude
order * j^2/(2l) * log p.  The following lemmas identify the S764 average log
with the actual l*-label average of rootThetaMagnitudeValue, so the no-go is
stated on the actual theta magnitudes, not only on a scalar model. -/

def w4SignedLabel (i : PaperThetaLabel l) : SignedLabel l.value :=
  ⟨(i.1 : Int) + 1, by
    constructor
    · have : (0 : Int) ≤ (i.1 : Int) := by exact_mod_cast Nat.zero_le i.1
      omega
    · have hi : i.1 < lStar l.value := i.2
      have hls : lStar l.value ≤ l.value := by
        unfold lStar
        omega
      omega⟩

theorem w4SignedLabel_gaussExponent (i : PaperThetaLabel l) :
    (gaussExponent (w4SignedLabel (l := l) i).1).toNat = (i.1 + 1)^2 := by
  have hval : (w4SignedLabel (l := l) i).1 = (i.1 : Int) + 1 := rfl
  rw [hval]
  unfold gaussExponent
  have hcast : ((i.1 : Int) + 1) ^ 2 = (((i.1 + 1)^2 : Nat) : Int) := by
    push_cast
    ring
  rw [hcast, Int.toNat_natCast]

theorem w4RootThetaMagnitudeValue_eq (i : PaperThetaLabel l) :
    rootThetaMagnitudeValue T b (w4SignedLabel (l := l) i) =
      w4ThetaExponent l i * ((qVFamily T b).order : Real) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold rootThetaMagnitudeValue qVFamPaperThetaTensorCoefficient
    w4ThetaExponent qVFamPaperRootCoefficient
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, nsmul_eq_mul]
  rw [w4SignedLabel_gaussExponent]
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  simp only [Nat.cast_one]
  push_cast
  field_simp [hl]

theorem paperThetaLabelAverage_mul_const (c : Real) (f : PaperThetaLabel l → Real) :
    paperThetaLabelAverage (l := l) (fun i => f i * c) =
      paperThetaLabelAverage (l := l) f * c := by
  unfold paperThetaLabelAverage
  change paperThetaLabelWeight l * (∑ i, f i * c) =
    (paperThetaLabelWeight l * ∑ i, f i) * c
  rw [← Finset.sum_mul]
  ring

/-- The actual l*-label average of the root theta magnitudes is the second
moment coefficient (l+1)/24 times order * log p. -/
theorem paperThetaLabelAverage_rootThetaMagnitudeValue_eq :
    paperThetaLabelAverage (l := l)
        (fun i => rootThetaMagnitudeValue T b (w4SignedLabel (l := l) i)) =
      ((qVFamily T b).order : Real) * w4AverageCoefficient l *
        Real.log (qVFamTensorP T b : Real) := by
  have hfun : (fun i => rootThetaMagnitudeValue T b (w4SignedLabel (l := l) i)) =
      (fun i => w4ThetaExponent l i *
        (((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real))) := by
    funext i
    rw [w4RootThetaMagnitudeValue_eq]
    ring
  rw [hfun]
  rw [paperThetaLabelAverage_mul_const]
  rw [w4ThetaLabelAverage_eq]
  ring

/-- S764's paperThetaAverageLog is exactly minus the actual l*-label average of
the root theta magnitudes. -/
theorem paperThetaAverageLog_eq_neg_rootThetaMagnitudeAverage :
    paperThetaAverageLog (l := l) T b =
      -(paperThetaLabelAverage (l := l)
        (fun i => rootThetaMagnitudeValue T b (w4SignedLabel (l := l) i))) := by
  rw [paperThetaLabelAverage_rootThetaMagnitudeValue_eq]
  unfold paperThetaAverageLog
  rw [w4AverageCoefficient_eq]

/-! ## 5. The hull log versus the l* average log -/

variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]
variable [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (LeanFormal.IUT.nativePlaceSelection T))

/-- The hull-min log is exactly the least-hull formula scalar paperQPilotLogLeast. -/
theorem paperThetaHullMinLog_eq_leastFormula :
    paperThetaHullMinLog (l := l) T b = paperQPilotLogLeast (l := l) T b := by
  unfold paperThetaHullMinLog paperQPilotLogLeast paperThetaHullMinCoefficient
    paperRootCoefficientFamily qVFamPaperRootCoefficient
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, nsmul_eq_mul]
  simp only [Nat.cast_one, one_mul]
  ring

/-- Positive identification: with the pure fractional scaling datum, the actual
least lambda-O hull log is the hull-extremum formula (S799), not a label average. -/
theorem paperLeastLambdaOHullLog_eq_leastFormula_of_data
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b)) :
    paperLeastLambdaOHullLog (l := l) T b μ =
      paperQPilotLogLeast (l := l) T b := by
  rw [paperLeastLambdaOHullLog_eq_formula (l := l) T b μ D]
  rfl

/-- The least-hull formula scalar is strictly negative for positive order and
positive log p. -/
theorem paperQPilotLogLeast_neg
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    paperQPilotLogLeast (l := l) T b < 0 := by
  rw [← paperThetaHullMinLog_eq_leastFormula (l := l) T b]
  unfold paperThetaHullMinLog
  have hminpos : 0 < paperThetaHullMinCoefficient (l := l) := by
    unfold paperThetaHullMinCoefficient
    have hlpos : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    positivity
  have hpos : 0 < ((qVFamily T b).order : Real) *
      paperThetaHullMinCoefficient (l := l) * Real.log (qVFamTensorP T b : Real) := by
    exact mul_pos (mul_pos horder hminpos) hlog
  nlinarith

/-- The l* average log is strictly below the least-hull formula scalar. -/
theorem paperThetaAverageLog_lt_paperQPilotLogLeast
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    paperThetaAverageLog (l := l) T b < paperQPilotLogLeast (l := l) T b := by
  rw [← paperThetaHullMinLog_eq_leastFormula (l := l) T b]
  exact paperThetaHullMinLog_gt_averageLog (l := l) T b horder hlog

/-- No-go: even with the exact least-hull log formula, the l* average log is
strictly smaller than the least lambda-O hull log.  Hence l* average = hull log
is false, not merely unproved. -/
theorem paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b))
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    paperThetaAverageLog (l := l) T b < paperLeastLambdaOHullLog (l := l) T b μ := by
  rw [paperLeastLambdaOHullLog_eq_leastFormula_of_data (l := l) T b μ D]
  exact paperThetaAverageLog_lt_paperQPilotLogLeast (l := l) T b horder hlog

theorem paperThetaAverageLog_ne_paperLeastLambdaOHullLog_of_data
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b))
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    paperThetaAverageLog (l := l) T b ≠ paperLeastLambdaOHullLog (l := l) T b μ :=
  ne_of_lt (paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data
    (l := l) T b μ D horder hlog)

/-- No-go in the actual theta magnitudes: the signed l*-average of the root
theta magnitudes is strictly smaller than the least lambda-O hull log. -/
theorem rootThetaMagnitudeAverage_lt_leastHullLog_of_data
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    (D : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b))
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    -(paperThetaLabelAverage (l := l)
        (fun i => rootThetaMagnitudeValue T b (w4SignedLabel (l := l) i))) <
      paperLeastLambdaOHullLog (l := l) T b μ := by
  rw [← paperThetaAverageLog_eq_neg_rootThetaMagnitudeAverage (l := l)]
  exact paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data
    (l := l) T b μ D horder hlog

#check w4ThetaLabelAverage_eq
#check w4HullMin_lt_weightedAverage_of_pos
#check stackMuRoot_orbitAverage_eq_zero
#check paperLeastLambdaOHullLog_eq_leastFormula_of_data
#check paperThetaAverageLog_lt_paperLeastLambdaOHullLog_of_data
#check paperThetaAverageLog_ne_paperLeastLambdaOHullLog_of_data
#check paperThetaAverageLog_eq_neg_rootThetaMagnitudeAverage
#check rootThetaMagnitudeAverage_lt_leastHullLog_of_data

end LeanFormal.IUT.XiFPaper.W4GaussSecondMomentNoGoActual

end
