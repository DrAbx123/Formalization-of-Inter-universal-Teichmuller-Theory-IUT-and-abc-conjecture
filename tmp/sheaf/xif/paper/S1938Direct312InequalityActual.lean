import tmp.sheaf.xif.paper.S1928BridgeAverageA0Actual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.S1905Unconditional312Actual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual

/-!
# S1938: the Corollary 3.12 target inequality  -|log q| <= -average  proved
# directly, without the S1904 procession bridge

Layer: **O** (original-text Theta-link / IUT III Corollary 3.12, Step (xi-f)).

## The question

S1905 reduces the unconditional Corollary 3.12 inequality at the actual q to the
S1904 procession bridge: s1905_unconditional_iff_firstMissing states that the
inequality, read on the assembled paper signed-hull datum, is *equivalent* to
the bridge.  S1928 then shows that the bridge at the actual S1902 hull and the
actual S1903 determinant is equivalent to a genuine arithmetic identity and is
false on the clipped region, i.e. it cannot be manufactured from the two actual
components.  Read naively, this would leave the target inequality

  -|log q| <= -average,  equivalently  average <= |log q|,

without a proof.

This file proves the inequality **directly**, with no bridge and no S1880
comparison.  The point is that on the determinant side the target is a purely
numerical statement about the S1903 procession average

  average = s1904ProcessionAverage (s1903ActualDeterminant l)

whose exact value is known from S1928:

  average = log 5 * (sum_j j^2) / l^4.

The signed labels are the integers j with |j| <= lStar l = (l - 1)/2, and
there are exactly l of them (SignedLabel.card_signedLabel), so

  sum_j j^2 <= l * lStar^2 <= l * l^2 = l^3,

hence

  average <= log 5 * l^3 / l^4 = log 5 / l <= log 5 <= |log q|,

because |log q| = localLogMagnitude S1487Cand >= log 5 (S1487) and l >= 5.
In fact average < 1, while 1 < log 5 <= |log q|, so the inequality holds with a
wide margin.  No Haar readout, no procession normalization and no arithmetic
identity is used.

## What is proved here (all with the actual objects)

1. [PROVED] **The label-square bound** sum_j (j.1)^2 <= l^3 (section 1).
2. [PROVED] **The sharp average bound** average <= log 5 / l and average < 1
   (section 2).  In particular the paper's necessary procession normalization
   average <= 1 -- which S1904 obtains only *under* the bridge
   (s1904_bridge_average_le_one) -- holds unconditionally at the actual S1903
   determinant.
3. [PROVED] **The target inequality** in the paper's -|log q| <= -average form,
   in the equivalent average <= |log q| form, and in the localLogMagnitude form
   (section 3).  The S1904 bridge is not used.
4. [PROVED] **The general criterion** (section 4): for *any* actual determinant
   whose procession average is at most log 5 -- in particular at most 1 -- the
   same inequality holds.  This is the form in which the paper-faithful
   determinant (S1939, built from the actual root packet) will consume the
   result: only its determinant-side normalization average <= 1 (equivalently
   average <= log 5) is needed to obtain Corollary 3.12's inequality, never the
   Haar bridge.
5. [PROVED] **The bridge is irrelevant to the inequality** (section 5): on the
   S1928 clipped region s1915ClosedForm T <= 0 -- when nonempty -- the bridge is
   *false* (s1928_bridge_false_of_closedForm_nonpos) while the target inequality
   still holds.  Hence on that region the inequality is strictly weaker than the
   bridge and the bridge cannot be recovered from it; the equivalence of S1905
   is a property of the assembled datum, not of the inequality.
6. [PROVED] **The same conclusion on the assembled S1905 datum** (section 5),
   re-derived *without* the S1880 route: for every bridge witness h,

     -|log q| <= OrigXiFSignedThetaHullLogVolume (S1905D T h),

   because the signed scalar of the assembled datum is -average and the witness
   is used only to *form* the datum.  The S1880 proof of this comparison goes
   through OrigXiFSignedThetaHullLogVolume_ge_neg_one; here the comparison is
   the numerical bound of section 3.

## What this does not claim

* This file does **not** assert that the paper's actual determinant is
  s1903ActualDeterminant l.  S1928 computes its average as
  log 5 * (sum_j j^2)/l^4 -- a rational multiple of log 5 with zero rational
  part -- and reduces the bridge at the actual fields to a genuine arithmetic
  identity between that number and the local q_v log-sum, so S1928 records this
  determinant as the q = 1/5 model rather than as the actual root packet.
  Constructing the paper-faithful determinant from the actual root packet is
  S1939; what section 4 shows is that S1939 only has to establish the
  determinant-side normalization average <= 1 to get 3.12's inequality.
* The S1904 bridge itself (hull Haar log-volume = ofReal average) remains open.
  Section 5 shows the inequality holds where the bridge provably fails, so it
  cannot be used to recover the bridge on that region.
* Consequently there is **no missing inequality**: the S1938 target is a
  theorem (s1938_target_not_missing).  What remains for the paper-level
  statement is the paper-faithful determinant (S1939) and, if one insists on
  reading the right-hand side as the actual hull log-volume rather than as
  -average, the bridge itself.

## Consumer note

Stating the inequality literally in another file requires the local
irreducibility Fact instance of the concrete Gaussian field
GaussianField = AdjoinRoot (X^2 + 1), exactly as in S1487/S1880; the theorems
below are stated with it in scope.

No sorry, admit, axiom, True/PUnit slot, or arbitrary datum is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1938Direct312InequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1903SignedHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1905Unconditional312Actual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1928BridgeAverageA0Actual
open scoped BigOperators

variable {l : PrimeGeFive}

/-- The concrete Gaussian field Q(i) is an AdjoinRoot, so its Field instance
needs the irreducibility fact; this is the same local instance used by S1487
and S1880 when reading the actual completion q. -/
local instance s1938GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1938FivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The label-square bound

The signed labels are the bounded integer representatives
SignedLabel l.value = {j : Int // -(lStar l.value) <= j <= lStar l.value}, and
there are l.value of them.  Hence every square is at most lStar l.value^2, and
lStar l.value < l.value. -/

/-- |j| <= lStar l for every signed label. -/
theorem s1938_abs_label_le (j : SignedLabel l.value) :
    |((j.1 : ℤ) : ℝ)| ≤ (lStar l.value : ℝ) := by
  have h1 : ((j.1 : ℤ) : ℝ) ≤ (lStar l.value : ℝ) := by
    exact_mod_cast j.2.2
  have h2 : -((lStar l.value : ℝ)) ≤ ((j.1 : ℤ) : ℝ) := by
    have h := j.2.1
    have h' : ((-(lStar l.value : ℤ) : ℤ) : ℝ) ≤ ((j.1 : ℤ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  exact abs_le.mpr ⟨h2, h1⟩

/-- The square of every label is at most lStar l^2. -/
theorem s1938_label_sq_le (j : SignedLabel l.value) :
    ((j.1 : ℤ) : ℝ) ^ 2 ≤ (lStar l.value : ℝ) ^ 2 := by
  have h := s1938_abs_label_le (l := l) j
  calc ((j.1 : ℤ) : ℝ) ^ 2 = |((j.1 : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (lStar l.value : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **The label-square bound**: sum_j j^2 <= l^3. -/
theorem s1938_sum_sq_le :
    (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2) ≤ (l.value : ℝ) ^ 3 := by
  have hstep : (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2) ≤
      ∑ _j : SignedLabel l.value, (lStar l.value : ℝ) ^ 2 :=
    Finset.sum_le_sum (fun j _ => s1938_label_sq_le (l := l) j)
  have hconst : (∑ _j : SignedLabel l.value, (lStar l.value : ℝ) ^ 2) =
      (l.value : ℝ) * (lStar l.value : ℝ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, SignedLabel.card_signedLabel l]
  have hstar0 : (0 : ℝ) ≤ (lStar l.value : ℝ) := Nat.cast_nonneg _
  have hstarle : (lStar l.value : ℝ) ≤ (l.value : ℝ) := by
    have h : lStar l.value ≤ l.value := (concreteLabel_star_lt l).le
    exact_mod_cast h
  have hsq : (lStar l.value : ℝ) ^ 2 ≤ (l.value : ℝ) ^ 2 :=
    pow_le_pow_left₀ hstar0 hstarle 2
  have hl0 : (0 : ℝ) ≤ (l.value : ℝ) := Nat.cast_nonneg _
  calc (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2)
      ≤ (l.value : ℝ) * (lStar l.value : ℝ) ^ 2 := hstep.trans (le_of_eq hconst)
    _ ≤ (l.value : ℝ) * (l.value : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hl0
    _ = (l.value : ℝ) ^ 3 := by ring

/-! ## 2. The average bound from the S1928 closed form -/

/-- log 5 > 1.  (This is Mathlib's Real.exp_one_lt_three read through
Real.log_lt_log; the project also has it as -log 5 < -1.) -/
theorem s1938_one_lt_log_five : (1 : ℝ) < Real.log 5 := by
  have h : Real.log (Real.exp 1) < Real.log 5 :=
    Real.log_lt_log (Real.exp_pos 1)
      (lt_trans Real.exp_one_lt_three (by norm_num))
  rwa [Real.log_exp] at h

/-- **The average is at most log 5 / l.**  This uses the S1928 closed form
s1928_average_eq and the label-square bound of section 1. -/
theorem s1938_average_le_log_five_div :
    s1904ProcessionAverage (s1903ActualDeterminant l) ≤ Real.log 5 / (l.value : ℝ) := by
  rw [s1928_average_eq]
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hl : 0 < (l.value : ℝ) := by exact_mod_cast l.prime.pos
  have h4 : 0 < (l.value : ℝ) ^ 4 := pow_pos hl 4
  rw [div_le_div_iff₀ h4 hl]
  have hS := s1938_sum_sq_le (l := l)
  have h1 : Real.log 5 * (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2) ≤
      Real.log 5 * (l.value : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_left hS hlog.le
  calc Real.log 5 * (∑ j : SignedLabel l.value, ((j.1 : ℤ) : ℝ) ^ 2) * (l.value : ℝ)
      ≤ Real.log 5 * (l.value : ℝ) ^ 3 * (l.value : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hl.le
    _ = Real.log 5 * (l.value : ℝ) ^ 4 := by ring

/-- log 5 / l <= log 5, since l >= 1 and log 5 >= 0. -/
theorem s1938_log_five_div_le_log_five :
    Real.log 5 / (l.value : ℝ) ≤ Real.log 5 := by
  have hl5 : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  have hl1 : (1 : ℝ) ≤ (l.value : ℝ) := by linarith
  exact div_le_self (Real.log_pos (by norm_num)).le hl1

/-- log 5 / l <= log 5 / 5, since l >= 5 and log 5 >= 0. -/
theorem s1938_log_five_div_le_five :
    Real.log 5 / (l.value : ℝ) ≤ Real.log 5 / 5 := by
  have hl5 : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  exact div_le_div_of_nonneg_left (Real.log_pos (by norm_num)).le (by norm_num) hl5

/-- **The average is at most log 5 / 5**: the explicit numerical chain
average <= log 5 / l <= log 5 / 5 of the S1928 closed form. -/
theorem s1938_average_le_log_five_div_five :
    s1904ProcessionAverage (s1903ActualDeterminant l) ≤ Real.log 5 / 5 :=
  (s1938_average_le_log_five_div (l := l)).trans
    (s1938_log_five_div_le_five (l := l))

/-- log 5 / 5 < 1. -/
theorem s1938_log_five_div_five_lt_one : Real.log 5 / 5 < 1 := by
  have hlog4 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith
  have : Real.log 5 / 5 ≤ 4 / 5 :=
    div_le_div_of_nonneg_right hlog4 (by norm_num)
  linarith

/-- **The average is strictly less than one**: the paper's necessary procession
normalization average <= 1 holds unconditionally at the actual S1903
determinant (S1904 obtains it only under the bridge). -/
theorem s1938_average_lt_one :
    s1904ProcessionAverage (s1903ActualDeterminant l) < 1 := by
  have hl : 0 < (l.value : ℝ) := by exact_mod_cast l.prime.pos
  have hl5 : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  have hlog4 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith
  have hloglt : Real.log 5 < (l.value : ℝ) := by linarith
  have hdiv : Real.log 5 / (l.value : ℝ) < 1 := (div_lt_one hl).mpr hloglt
  have hle := s1938_average_le_log_five_div (l := l)
  linarith

/-! ## 3. The target inequality -|log q| <= -average

The paper's -|log q| is -localLogMagnitude S1487Cand, and
localLogMagnitude S1487Cand >= log 5 (S1487Cand_magnitude_ge_log_five). -/

/-- |log q| = localLogMagnitude S1487Cand for the actual completion q. -/
theorem s1938_abs_log_q_eq_magnitude :
    |Real.log ‖S1487Cand.q‖| = localLogMagnitude S1487Cand :=
  abs_localSignedLog S1487Cand

/-- log 5 <= |log q|. -/
theorem s1938_log_five_le_abs_log_q :
    Real.log 5 ≤ |Real.log ‖S1487Cand.q‖| := by
  rw [s1938_abs_log_q_eq_magnitude]
  exact S1487Cand_magnitude_ge_log_five

/-- **The target inequality, average <= |log q| form.** -/
theorem s1938_average_le_abs_log_q :
    s1904ProcessionAverage (s1903ActualDeterminant l) ≤ |Real.log ‖S1487Cand.q‖| :=
  (s1938_average_le_log_five_div (l := l)).trans
    ((s1938_log_five_div_le_log_five (l := l)).trans s1938_log_five_le_abs_log_q)

/-- **The inequality is strict**: average < |log q|, because average < 1 <
log 5 <= |log q|. -/
theorem s1938_average_lt_abs_log_q :
    s1904ProcessionAverage (s1903ActualDeterminant l) < |Real.log ‖S1487Cand.q‖| := by
  have h1 := s1938_average_lt_one (l := l)
  have h2 := s1938_one_lt_log_five
  have h3 := s1938_log_five_le_abs_log_q
  linarith

/-- **The target inequality in the paper's own form**: -|log q| <= -average.
No S1904 bridge is used. -/
theorem s1938_neg_abs_log_q_le_neg_average :
    -|Real.log ‖S1487Cand.q‖| ≤
      -s1904ProcessionAverage (s1903ActualDeterminant l) := by
  linarith [s1938_average_le_abs_log_q (l := l)]

/-- The same comparison in the paper's localLogMagnitude form. -/
theorem s1938_neg_magnitude_le_neg_average :
    -localLogMagnitude S1487Cand ≤
      -s1904ProcessionAverage (s1903ActualDeterminant l) := by
  rw [← s1938_abs_log_q_eq_magnitude]
  exact s1938_neg_abs_log_q_le_neg_average (l := l)

/-- **The S1938 target, named**: the Corollary 3.12 inequality at the actual
completion q and the actual S1903 determinant average. -/
def S1938Target (l : PrimeGeFive) : Prop :=
  -|Real.log ‖S1487Cand.q‖| ≤ -s1904ProcessionAverage (s1903ActualDeterminant l)

/-- **The S1938 target is a theorem** (not a missing datum). -/
theorem s1938_target : S1938Target l :=
  s1938_neg_abs_log_q_le_neg_average

/-- **The direct 3.12 package** at the actual S1903 determinant: the inequality
in both forms, together with the unconditional normalization average < 1. -/
theorem s1938_direct312 :
    s1904ProcessionAverage (s1903ActualDeterminant l) ≤ |Real.log ‖S1487Cand.q‖| ∧
      -|Real.log ‖S1487Cand.q‖| ≤
        -s1904ProcessionAverage (s1903ActualDeterminant l) ∧
        s1904ProcessionAverage (s1903ActualDeterminant l) < 1 :=
  ⟨s1938_average_le_abs_log_q (l := l),
    s1938_neg_abs_log_q_le_neg_average (l := l),
    s1938_average_lt_one (l := l)⟩

/-- **There is no missing inequality**: the S1938 target proposition is a
theorem, not a datum. -/
theorem s1938_target_not_missing :
    ¬ (|Real.log ‖S1487Cand.q‖| < s1904ProcessionAverage (s1903ActualDeterminant l)) :=
  not_lt.mpr (s1938_average_le_abs_log_q (l := l))

/-! ## 4. The general criterion for a paper-faithful determinant

The inequality does not depend on the particular S1903 determinant: any actual
determinant whose procession average is at most log 5 (in particular at most 1,
the paper's determinant-side normalization) satisfies it.  This is the
interface S1939 has to meet. -/

/-- **General 3.12 criterion.**  Any actual determinant with procession average
at most log 5 satisfies -|log q| <= -average. -/
theorem s1938_neg_abs_log_q_le_neg_average_of_le
    (P : SignedHullLogActual (SignedLabel l.value))
    (hP : s1904ProcessionAverage P ≤ Real.log 5) :
    -|Real.log ‖S1487Cand.q‖| ≤ -s1904ProcessionAverage P := by
  have hq := s1938_log_five_le_abs_log_q
  linarith

/-- **General 3.12 criterion, normalization form.**  Any actual determinant
whose procession average is at most 1 -- the paper's necessary normalization
(S1904) -- satisfies -|log q| <= -average, without any Haar readout. -/
theorem s1938_neg_abs_log_q_le_neg_average_of_average_le_one
    (P : SignedHullLogActual (SignedLabel l.value))
    (hP : s1904ProcessionAverage P ≤ 1) :
    -|Real.log ‖S1487Cand.q‖| ≤ -s1904ProcessionAverage P := by
  have hq := s1938_log_five_le_abs_log_q
  have h1 : (1 : ℝ) < Real.log 5 := s1938_one_lt_log_five
  linarith

/-! ## 5. Independence from the S1904 bridge -/

variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **The inequality holds where the bridge provably fails.**  On the S1928
clipped region s1915ClosedForm T <= 0 the S1904 bridge at the actual S1902 hull
and S1903 determinant is false, while the target inequality still holds.  Hence
the inequality is strictly weaker than the bridge and the S1905 equivalence is
a property of the assembled datum, not of the inequality. -/
theorem s1938_inequality_without_bridge
    (h : s1915ClosedForm T ≤ 0) :
    s1904ProcessionAverage (s1903ActualDeterminant l) ≤ |Real.log ‖S1487Cand.q‖| ∧
      ¬ S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) :=
  ⟨s1938_average_le_abs_log_q (l := l),
    s1928_bridge_false_of_closedForm_nonpos T h⟩

/-- The signed scalar of the assembled S1905 datum is minus the S1903
determinant average. -/
theorem s1938_S1905D_signed (h : S1905FirstMissing T) :
    OrigXiFSignedThetaHullLogVolume (S1905D T h) =
      -s1904ProcessionAverage (s1903ActualDeterminant l) := by
  rw [OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  rfl

/-- **The Corollary 3.12 inequality on the assembled S1905 datum, re-derived
without the S1880 route.**  The bridge witness h is used only to form the
datum; the comparison itself is the numerical bound of section 3. -/
theorem s1938_S1905D_inequality (h : S1905FirstMissing T) :
    -|Real.log ‖S1487Cand.q‖| ≤ OrigXiFSignedThetaHullLogVolume (S1905D T h) := by
  rw [s1938_S1905D_signed T h]
  exact s1938_neg_abs_log_q_le_neg_average (l := l)

/-- The same comparison on the assembled S1905 datum in the paper's
localLogMagnitude form. -/
theorem s1938_S1905D_inequality_magnitude (h : S1905FirstMissing T) :
    -localLogMagnitude S1487Cand ≤ OrigXiFSignedThetaHullLogVolume (S1905D T h) := by
  rw [s1938_S1905D_signed T h]
  exact s1938_neg_magnitude_le_neg_average (l := l)

/-! ## 6. Axiom probes -/

#print axioms s1938_abs_label_le
#print axioms s1938_sum_sq_le
#print axioms s1938_average_le_log_five_div
#print axioms s1938_average_le_log_five_div_five
#print axioms s1938_log_five_div_five_lt_one
#print axioms s1938_average_lt_one
#print axioms S1938Target
#print axioms s1938_target
#print axioms s1938_abs_log_q_eq_magnitude
#print axioms s1938_log_five_le_abs_log_q
#print axioms s1938_average_le_abs_log_q
#print axioms s1938_average_lt_abs_log_q
#print axioms s1938_neg_abs_log_q_le_neg_average
#print axioms s1938_neg_magnitude_le_neg_average
#print axioms s1938_direct312
#print axioms s1938_target_not_missing
#print axioms s1938_neg_abs_log_q_le_neg_average_of_le
#print axioms s1938_neg_abs_log_q_le_neg_average_of_average_le_one
#print axioms s1938_inequality_without_bridge
#print axioms s1938_S1905D_signed
#print axioms s1938_S1905D_inequality
#print axioms s1938_S1905D_inequality_magnitude

end LeanFormal.IUT.XiFPaper.S1938Direct312InequalityActual
