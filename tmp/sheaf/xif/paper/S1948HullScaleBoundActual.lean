import tmp.sheaf.xif.paper.S1939RootPacketDeterminantActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.FinitePlaceQCandidateValuationActual
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# S1948: the actual hull-scale bound of S1939, the exact qVFamily reduction,
# and the precise first missing

Layer: O (original-text Theta-link / Step (xi-f), Corollary 3.12).

## The input consumed

S1939 constructs the actual root-packet determinant with the paper l*
procession and proves, unconditionally,

  average (s1939Procession T) = s1915ClosedForm T = 1 + s1939BadLog T,

where

  s1939BadLog T = sum_b (s1915LocalDegree T b) * log (s1928RootNorm T b),
  s1928RootNorm T b = ||rootNormedElement T b|| = ||q_b||^(1/(2l)),

and the hull-scale requirement (every packet scale at least one) is exactly the
real inequality

  s1939HullScaleBound T :  (l*)^2 * |s1939BadLog T| <= M,
  l* = (l-1)/2,  M = l*(l+1)/12.

When this bound holds, S1939 produces the determinant and the S1904 bridge and
the S1880 Corollary 3.12 inequality follow.  The bound is the only unproved
input of that route.

## What is proved here (no fake)

1. [PROVED, unconditional] The bound is exactly a quantitative lower bound on
   the actual unclipped bad-place closed form:

     s1939HullScaleBound T  <->  1 - M/(l*)^2 <= s1915ClosedForm T.

   Since s1928_closedForm_lt_one gives s1915ClosedForm T < 1 unconditionally,
   the bound is precisely the missing lower half of the closed-form range.
   The threshold is at most 5/8 for every l >= 5.

2. [PROVED, unconditional] The exact number-field degree/determinant identity

     2*l <= [L_b : K_b] * order(q_b),

   where L_b is the actual root extension of K_b and order(q_b) is the actual
   positive qVFamily order.  Proof: for the root r of q_b, the field norm
   N_{L_b/K_b}(r) satisfies N^(2l) = q_b^[L_b:K_b]; applying the actual
   integer-valued completion valuation yields the integer identity
   n * order(q_b) = 2*l * a with a > 0, hence the real inequality above.

3. [PROVED, conditional] The precise first missing is the normalized
   norm/valuation comparison

     S1948NormValuationComparison T b :
       ||q_b|| = absNorm(b) ^ (-(order(q_b) : R) / [K_b : Q_p]),

   equivalently log ||q_b|| = -(order(q_b) * log absNorm(b)) / [K_b : Q_p].
   It is the actual-place specialization of the project's already named missing
   analytic lemma Example36.NormalizedLogNormComparison (the normalized
   completion norm has not been identified with the canonical valuation norm in
   the current tree; the file that attempts it,
   GeneralNormalizedNormBySpectralUniqueness, does not build).

   Granting this comparison, every bad-place term satisfies

     [K_b : Q_p] * log ||rootNormedElement_b||  <=  -log 2,

   hence

     s1939BadLog T <= -log 2     and     NOT s1939HullScaleBound T.

   So the S1939 hull-scale bound is not merely unproved: under the standard
   (and mathematically true) normalized norm/valuation comparison it is
   false.  The S1939 route cannot be closed by proving the bound; its
   obstruction is the quantitative lower bound on the actual bad-place q-norms,
   which points the other way.

4. [PROVED, unconditional] The current qualitative interface (every root norm
   in (0,1), its log nonpositive, closed form < 1) is recorded and does not
   contain any lower bound on the negative root log; the bound is exactly such
   a lower bound, so it is not derivable from the current interface.  The
   precise first missing is named S1948FirstMissing below.

No sorry, axiom, True/PUnit slot, or fake norm value is used.  The only
unproved input is the named comparison S1948NormValuationComparison.

## Consumer

S1939RootPacketDeterminantActual (s1939FirstMissing_iff_qNorms,
s1939Determinant, s1939_cor312): this file shows that closing the S1939 first
missing would refute it, so the paper-level Corollary 3.12 must use the S1940
clipped-hull determinant (or another normalization) rather than the unclipped
root packet.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1948HullScaleBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1928BridgeAverageA0Actual
open LeanFormal.IUT.XiFPaper.S1930CompareA0AverageActual
open LeanFormal.IUT.XiFPaper.S1939RootPacketDeterminantActual
open LeanFormal.IUT.XiFPaper.FinitePlaceQCandidateValuationActual
open scoped BigOperators

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]

/-! ## 1. The bound and the closed-form lower bound -/

/-- The S1939 hull-scale bound, restated in this file. -/
abbrev S1948HullScaleBound : Prop := s1939HullScaleBound T

/-- The bound is the S1939 bound. -/
theorem s1948HullScaleBound_iff :
    S1948HullScaleBound T ↔ s1939HullScaleBound T := Iff.rfl

/-- The actual qVFamily form of the bound. -/
theorem s1948HullScaleBound_iff_qNorms :
    S1948HullScaleBound T ↔
      (lStar l.value : Real) ^ 2 *
          |(1 / (2 * (l.value : Real))) *
            ∑ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
              (s1915LocalDegree T b : Real) *
                Real.log ‖(sourceRootQUnit T b : rootBase T b)‖|
        ≤ s1939MeanSquare l :=
  s1939FirstMissing_iff_qNorms T

/-- The bound is exactly the missing lower half of the actual closed form.
S1928 proves s1915ClosedForm T = 1 + s1939BadLog T and s1939BadLog T < 0
unconditionally, so |s1939BadLog T| = -s1939BadLog T. -/
theorem s1948HullScaleBound_iff_closedForm_lower :
    S1948HullScaleBound T ↔
      1 - s1939MeanSquare l / (lStar l.value : Real) ^ 2 ≤ s1915ClosedForm T := by
  have hS := s1939BadLog_neg T
  have hls : 0 < (lStar l.value : Real) := by
    exact_mod_cast s1930_lStar_pos l
  have hls2 : 0 < (lStar l.value : Real) ^ 2 := by positivity
  have hclosed : s1915ClosedForm T = 1 + s1939BadLog T :=
    s1939_closedForm_eq_badLog T
  have habs : |s1939BadLog T| = -s1939BadLog T := abs_of_neg hS
  unfold S1948HullScaleBound s1939HullScaleBound
  rw [hclosed, habs]
  constructor
  · intro h
    have h' : (lStar l.value : Real) ^ 2 * (-s1939BadLog T) ≤ s1939MeanSquare l := h
    have hdiv : -s1939BadLog T ≤ s1939MeanSquare l / (lStar l.value : Real) ^ 2 := by
      rw [le_div_iff₀ hls2]
      simpa only [mul_comm] using h'
    linarith
  · intro h
    have h' : -s1939BadLog T ≤ s1939MeanSquare l / (lStar l.value : Real) ^ 2 := by
      linarith
    have := (le_div_iff₀ hls2).mp h'
    simpa only [mul_comm] using this

/-- The threshold M/(l*)^2 is at most 5/8 for every prime l >= 5. -/
theorem s1948_meanSquare_div_lStar_sq_le_five_eighths :
    s1939MeanSquare l / (lStar l.value : Real) ^ 2 ≤ 5 / 8 := by
  have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
  have hl : (0 : Real) < (l.value : Real) := by linarith
  rw [s1939_lStar_eq l]
  unfold s1939MeanSquare
  have hb : (0 : Real) < (((l.value : Real) - 1) / 2) ^ 2 := by
    have hpos : (0 : Real) < ((l.value : Real) - 1) / 2 := by linarith
    positivity
  rw [div_le_div_iff₀ hb (by norm_num)]
  nlinarith [sq_nonneg ((l.value : Real) - 5)]

/-- log 2 > 5/8. -/
theorem s1948_log_two_gt_five_eighths : (5 / 8 : Real) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

/-- The bound implies the actual closed form is positive. -/
theorem s1948HullScaleBound_imp_closedForm_pos (h : S1948HullScaleBound T) :
    0 < s1915ClosedForm T :=
  s1939_closedForm_pos T h

/-- The bound implies the bad log magnitude is below one. -/
theorem s1948HullScaleBound_imp_abs_badLog_lt_one (h : S1948HullScaleBound T) :
    |s1939BadLog T| < 1 :=
  s1939_absBadLog_lt_one T h

/-- The bound implies the actual closed form is at least 3/8 (for l >= 5). -/
theorem s1948HullScaleBound_imp_closedForm_ge_three_eighths
    (h : S1948HullScaleBound T) : (3 / 8 : Real) ≤ s1915ClosedForm T := by
  have hiff := (s1948HullScaleBound_iff_closedForm_lower T).mp h
  have hle := s1948_meanSquare_div_lStar_sq_le_five_eighths (l := l)
  have h2 : (3 / 8 : Real) ≤ 1 - s1939MeanSquare l / (lStar l.value : Real) ^ 2 := by
    linarith
  linarith

/-- The unconditional upper half: the actual closed form is always < 1. -/
theorem s1948_closedForm_lt_one : s1915ClosedForm T < 1 :=
  s1928_closedForm_lt_one T

/-- The actual closed form is always at most one. -/
theorem s1948_closedForm_le_one : s1915ClosedForm T ≤ 1 :=
  le_of_lt (s1948_closedForm_lt_one T)

/-! ## 2. The exact degree/determinant identity at each bad place -/

/-- The canonical integer-valued valuation on the actual completion. -/
noncomputable def s1948CanonicalValuation (b : Bad (LeanFormal.IUT.nativePlaceSelection T)) :
    Valuation (Completion (qVFamTensorPlace T b)) (WithZero (Multiplicative Int)) :=
  Valued.v

/-- The valuation of the actual qVFamily unit is exp (-order). -/
theorem s1948CanonicalValuation_q
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T)) :
    s1948CanonicalValuation T b ((qVFamily T b).q : Completion (qVFamTensorPlace T b)) =
      WithZero.exp (-((qVFamily T b).order : Int)) := by
  have h := qValuation_eq_exp_neg_exponent (qVFamily T b)
  have hn : ((qVFamily T b).order : Int) = (qVFamily T b).exponent := by
    unfold FinitePlaceQCandidate.order
    exact Int.toNat_of_nonneg (le_of_lt (qVFamily T b).exponent_pos)
  rw [hn]
  exact h

/-- The real degree inequality: 2*l <= [L_b : K_b] * order(q_b). -/
theorem s1948_two_l_le_finrank_mul_order
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T)) :
    2 * (l.value : Real) ≤
      (Module.finrank (rootBase T b) (rootNormedExtension T b) : Real) *
        ((qVFamily T b).order : Real) := by
  classical
  letI hfree : Module.Free (rootBase T b) (rootNormedExtension T b) :=
    Module.Free.of_divisionRing _ _
  letI hfin : Module.Finite (rootBase T b) (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensional (T := T) (b := b)
  set n : Nat := Module.finrank (rootBase T b) (rootNormedExtension T b)
  set r : rootNormedExtension T b :=
    ⟨rootNormedElement T b, rootNormedElement_mem T b⟩
  set q : rootBase T b := (sourceRootQUnit T b : rootBase T b)
  have hr0 : r ≠ 0 := by
    intro h
    have h' : (rootNormedElement T b : rootNormedAmbient T b) = 0 := congrArg Subtype.val h
    exact Units.ne_zero (sourceRoot T b) h'
  have hpow : r ^ (2 * l.value) = algebraMap (rootBase T b) (rootNormedExtension T b) q := by
    apply Subtype.ext
    change (rootNormedElement T b) ^ (2 * l.value) =
      (algebraMap (rootBase T b) (rootNormedExtension T b) q : rootNormedAmbient T b)
    rw [rootNormedElement_pow]
    dsimp [q, rootBase, sourceRootField, NormalizedCompletion, rootNormedAmbient]
    simp only [unitToAlgClosed, Units.val_mk0]
    rfl
  have hNpow : (Algebra.norm (rootBase T b) r) ^ (2 * l.value) = q ^ n := by
    have h1 : (Algebra.norm (rootBase T b) r) ^ (2 * l.value) =
        Algebra.norm (rootBase T b) (r ^ (2 * l.value)) :=
      (map_pow (Algebra.norm (rootBase T b)) r (2 * l.value)).symm
    rw [h1, hpow, Algebra.norm_algebraMap]
  let v : Valuation (rootBase T b) (WithZero (Multiplicative Int)) :=
    s1948CanonicalValuation T b
  have hvq : v q = WithZero.exp (-((qVFamily T b).order : Int)) := by
    rw [show q = ((qVFamily T b).q : rootBase T b) from rfl]
    exact s1948CanonicalValuation_q T b
  have hveq : (v (Algebra.norm (rootBase T b) r)) ^ (2 * l.value) = (v q) ^ n := by
    rw [← Valuation.map_pow, ← Valuation.map_pow]
    exact congrArg v hNpow
  have hlog := congrArg WithZero.log hveq
  simp only [WithZero.log_pow] at hlog
  have hm : WithZero.log (v q) = -((qVFamily T b).order : Int) := by
    rw [hvq, WithZero.log_exp]
  rw [hm] at hlog
  have h2 : (2 * (l.value : Int)) * (-WithZero.log (v (Algebra.norm (rootBase T b) r))) =
      (n : Int) * ((qVFamily T b).order : Int) := by
    have h2' : (2 * (l.value : Int)) * WithZero.log (v (Algebra.norm (rootBase T b) r)) =
        (n : Int) * (-((qVFamily T b).order : Int)) := by
      simpa [smul_eq_mul] using hlog
    linarith
  have ha_pos : 0 < -WithZero.log (v (Algebra.norm (rootBase T b) r)) := by
    have hnpos : (0 : Int) < n := by exact_mod_cast Module.finrank_pos
    have hordpos : (0 : Int) < ((qVFamily T b).order : Int) := by
      exact_mod_cast (qVFamily T b).order_pos
    have h2l : (0 : Int) < 2 * (l.value : Int) := by
      have : (0 : Int) < l.value := by exact_mod_cast l.prime.pos
      linarith
    have hprod : 0 < (n : Int) * ((qVFamily T b).order : Int) := mul_pos hnpos hordpos
    rw [← h2] at hprod
    by_contra hle
    push Not at hle
    nlinarith
  have ha1 : (1 : Int) ≤ -WithZero.log (v (Algebra.norm (rootBase T b) r)) := by omega
  have h3 : (2 * (l.value : Int)) ≤ (n : Int) * ((qVFamily T b).order : Int) := by
    rw [← h2]
    calc (2 * (l.value : Int)) = (2 * (l.value : Int)) * 1 := by ring
      _ ≤ (2 * (l.value : Int)) * (-WithZero.log (v (Algebra.norm (rootBase T b) r))) :=
          mul_le_mul_of_nonneg_left ha1 (by positivity)
  have h3' : (2 * (l.value : Real)) ≤ (n : Real) * ((qVFamily T b).order : Real) := by
    exact_mod_cast h3
  simpa [n] using h3'

/-! ## 3. The exact first missing: the normalized norm/valuation comparison -/

/-- The per-place normalized norm/valuation comparison.  The norm of the
actual qVFamily unit is the canonical residue norm raised to
-order / [K_b : Q_p].  This is the concrete actual-place form of the missing
Example36.NormalizedLogNormComparison. -/
def S1948NormValuationComparison
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T)) : Prop :=
  ‖(sourceRootQUnit T b : rootBase T b)‖ =
    (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) ^
      (-((qVFamily T b).order : Real) /
        (Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) : Real))

/-- The comparison in logarithmic form. -/
theorem s1948_log_norm_of_comparison
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T))
    (h : S1948NormValuationComparison T b) :
    Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ =
      -(((qVFamily T b).order : Real) *
          Real.log (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real)) /
        (Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) : Real) := by
  have habs : (1 : Real) <
      (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm
      (qVFamTensorPlace T b).maximalIdeal
  have hD : (0 : Real) <
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b) : Real) := by
    exact_mod_cast Module.finrank_pos
  rw [h, Real.log_rpow (lt_trans zero_lt_one habs)]
  ring

/-- The per-place logarithmic term bound.  Granting the normalized
norm/valuation comparison, the contribution of b to the actual bad log is at
most -log 2. -/
theorem s1948_term_le_neg_log_two
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T))
    (h : S1948NormValuationComparison T b) :
    (s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b) ≤ - Real.log 2 := by
  classical
  set D : Nat := Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b)
  set n : Nat := Module.finrank (rootBase T b) (rootNormedExtension T b)
  have hDpos : (0 : Real) < (D : Real) := by exact_mod_cast Module.finrank_pos
  have hd : (s1915LocalDegree T b : Real) = (D : Real) * (n : Real) := by
    unfold s1915LocalDegree
    exact_mod_cast (Module.finrank_mul_finrank ℚ_[(qVFamTensorP T b)]
      (rootBase T b) (rootNormedExtension T b)).symm
  have h2l : (0 : Real) < 2 * (l.value : Real) := by
    have : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
    linarith
  have hrho2l : (s1928RootNorm T b) ^ (2 * l.value) =
      ‖(sourceRootQUnit T b : rootBase T b)‖ :=
    s1928RootNorm_pow_twoL T b
  have hlogrho : Real.log (s1928RootNorm T b) =
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ / (2 * (l.value : Real)) := by
    have h := congrArg Real.log hrho2l
    rw [Real.log_pow, Nat.cast_mul] at h
    norm_num at h
    rw [eq_div_iff (ne_of_gt h2l)]
    linarith
  have hlogq := s1948_log_norm_of_comparison T b h
  have habs : (1 : Real) <
      (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm
      (qVFamTensorPlace T b).maximalIdeal
  have habslog : 0 < Real.log
      (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) :=
    Real.log_pos habs
  have hnm : (2 * (l.value : Real)) ≤ (n : Real) * ((qVFamily T b).order : Real) := by
    simpa [n] using s1948_two_l_le_finrank_mul_order T b
  have hcoef : (1 : Real) ≤
      (n : Real) * ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
    rw [le_div_iff₀ h2l]
    simpa [mul_comm] using hnm
  calc (s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b)
      = ((D : Real) * (n : Real)) *
          (Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ / (2 * (l.value : Real))) := by
        rw [hd, hlogrho]
    _ = -(((n : Real) * ((qVFamily T b).order : Real)) / (2 * (l.value : Real))) *
          Real.log (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) := by
        rw [hlogq]
        have hDne : (D : Real) ≠ 0 := ne_of_gt hDpos
        dsimp only [D] at hDne ⊢
        have h2lne : (2 * (l.value : Real)) ≠ 0 := ne_of_gt h2l
        field_simp [hDne, h2lne]
    _ ≤ -Real.log (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) := by
        have hneg : -(((n : Real) * ((qVFamily T b).order : Real)) / (2 * (l.value : Real))) *
            Real.log (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real)
            ≤ -Real.log (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) := by
          have hmul := mul_le_mul_of_nonneg_right hcoef (le_of_lt habslog)
          nlinarith
        exact hneg
    _ ≤ -Real.log 2 := by
        have h2 : (2 : Real) ≤
            (Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal : Real) := by
          have h1 : (2 : Nat) ≤ Ideal.absNorm
              (qVFamTensorPlace T b).maximalIdeal.asIdeal := by
            have hlt : (1 : Nat) < Ideal.absNorm
                (qVFamTensorPlace T b).maximalIdeal.asIdeal := by
              exact_mod_cast habs
            omega
          exact_mod_cast h1
        have := Real.log_le_log (by norm_num : (0:Real) < 2) h2
        linarith

/-- The precise first missing: the normalized norm/valuation comparison at
every bad place. -/
def S1948FirstMissing : Prop :=
  ∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T), S1948NormValuationComparison T b

/-- The first missing is literally the family of comparisons. -/
theorem s1948FirstMissing_iff :
    S1948FirstMissing T ↔
      ∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
        S1948NormValuationComparison T b := Iff.rfl

/-- The bad log is at most -log 2 under the comparison. -/
theorem s1948_badLog_le_neg_log_two (h : S1948FirstMissing T) :
    s1939BadLog T ≤ - Real.log 2 := by
  classical
  haveI hne : Nonempty (Bad (LeanFormal.IUT.nativePlaceSelection T)) := by
    obtain ⟨p, hp⟩ := nativePlaceSelection_nonempty T
    exact ⟨⟨p, hp⟩⟩
  have hterm : ∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b) ≤ - Real.log 2 :=
    fun b => s1948_term_le_neg_log_two T b (h b)
  have hsum : s1939BadLog T ≤
      ∑ _b : Bad (LeanFormal.IUT.nativePlaceSelection T), (- Real.log 2) := by
    unfold s1939BadLog
    exact Finset.sum_le_sum (fun b _ => hterm b)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (1 : Real) ≤
      (Finset.univ : Finset (Bad (LeanFormal.IUT.nativePlaceSelection T))).card := by
    have : 0 < (Finset.univ : Finset (Bad (LeanFormal.IUT.nativePlaceSelection T))).card :=
      Finset.card_pos.mpr Finset.univ_nonempty
    exact_mod_cast this
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hstep : (Finset.univ : Finset (Bad (LeanFormal.IUT.nativePlaceSelection T))).card *
      (- Real.log 2) ≤ - Real.log 2 := by
    nlinarith
  linarith

/-- The S1939 hull-scale bound is false under the first missing. -/
theorem s1948_not_hullScaleBound_of_firstMissing (h : S1948FirstMissing T) :
    ¬ S1948HullScaleBound T := by
  intro hb
  have hS := s1948_badLog_le_neg_log_two T h
  have hSneg : s1939BadLog T < 0 := s1939BadLog_neg T
  have habs : |s1939BadLog T| = -s1939BadLog T := abs_of_neg hSneg
  have hlog2 : Real.log 2 > 5 / 8 := s1948_log_two_gt_five_eighths
  have hls : 0 < (lStar l.value : Real) ^ 2 := by
    have hpos := s1930_lStar_pos l
    have : (0 : Real) < (lStar l.value : Real) := by exact_mod_cast hpos
    positivity
  have hbig : s1939MeanSquare l < (lStar l.value : Real) ^ 2 * |s1939BadLog T| := by
    have h1 : (5 / 8 : Real) * (lStar l.value : Real) ^ 2 <
        Real.log 2 * (lStar l.value : Real) ^ 2 := by
      exact mul_lt_mul_of_pos_right hlog2 hls
    have h2 : s1939MeanSquare l ≤ (5 / 8 : Real) * (lStar l.value : Real) ^ 2 := by
      have hle := s1948_meanSquare_div_lStar_sq_le_five_eighths (l := l)
      rw [div_le_iff₀ (by positivity)] at hle
      simpa [mul_comm] using hle
    have h3 : Real.log 2 * (lStar l.value : Real) ^ 2 ≤
        |s1939BadLog T| * (lStar l.value : Real) ^ 2 := by
      have h4 : Real.log 2 ≤ |s1939BadLog T| := by
        rw [habs]
        linarith
      exact mul_le_mul_of_nonneg_right h4 (le_of_lt hls)
    have h5 : Real.log 2 * (lStar l.value : Real) ^ 2 ≤
        (lStar l.value : Real) ^ 2 * |s1939BadLog T| := by
      simpa [mul_comm] using h3
    linarith
  exact (not_le.mpr hbig) hb

/-- The exact first missing: the bound is refuted as soon as the normalized
norm/valuation comparison at the bad places is supplied; the comparison is the
only unproved input of this file. -/
theorem s1948_precise_first_missing :
    S1948FirstMissing T → ¬ s1939HullScaleBound T :=
  s1948_not_hullScaleBound_of_firstMissing T

/-! ## 4. The current qualitative interface -/

/-- The unconditional qualitative data currently available for the actual bad
places and the closed form: every root norm lies in (0,1), its log is
nonpositive, and the closed form is below one.  None of these gives a lower
bound on the negative root log. -/
def S1948QualitativeInterface : Prop :=
  (∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
      0 < s1928RootNorm T b ∧ s1928RootNorm T b < 1) ∧
    (∀ b : Bad (LeanFormal.IUT.nativePlaceSelection T),
      Real.log (s1928RootNorm T b) ≤ 0) ∧
      s1915ClosedForm T < 1

/-- The qualitative interface is proved unconditionally from the actual
qVFamily data. -/
theorem s1948_qualitativeInterface : S1948QualitativeInterface T := by
  refine ⟨?_, ?_, s1928_closedForm_lt_one T⟩
  · intro b
    exact ⟨s1928RootNorm_pos T b, s1928RootNorm_lt_one T b⟩
  · intro b
    exact Real.log_nonpos (le_of_lt (s1928RootNorm_pos T b))
      (le_of_lt (s1928RootNorm_lt_one T b))

/-- The bound implies a strictly positive lower bound on the closed form,
which the qualitative interface does not contain. -/
theorem s1948_bound_imp_lower :
    S1948HullScaleBound T →
      (3 / 8 : Real) ≤ s1915ClosedForm T :=
  s1948HullScaleBound_imp_closedForm_ge_three_eighths T

/-! ## 5. Axiom probes -/

#print axioms s1948HullScaleBound_iff_closedForm_lower
#print axioms s1948_meanSquare_div_lStar_sq_le_five_eighths
#print axioms s1948_log_two_gt_five_eighths
#print axioms s1948_two_l_le_finrank_mul_order
#print axioms s1948_log_norm_of_comparison
#print axioms s1948_term_le_neg_log_two
#print axioms s1948_badLog_le_neg_log_two
#print axioms s1948_not_hullScaleBound_of_firstMissing
#print axioms s1948_precise_first_missing
#print axioms s1948_qualitativeInterface

end LeanFormal.IUT.XiFPaper.S1948HullScaleBoundActual
