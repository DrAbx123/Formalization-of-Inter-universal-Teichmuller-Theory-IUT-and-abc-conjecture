import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.S1903SignedHullActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.RootTensorHaarTransportActual
import tmp.sheaf.xif.paper.S1905Unconditional312Actual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge

/-!
# S1928: the S1904 procession bridge at the actual S1902 hull and the actual
# S1903 determinant -- exact closed forms and the exact first missing

Layer: **O** (original-text Theta-link / Step (xi-f), Corollary 3.12).

## The question

S1915 proves that the S1904 procession bridge at the actual S1902 theta hull is
*exactly* the scalar identity

  S1904ProcessionBridge (s1902ActualThetaHull T) P  <->  average P = s1915A0 T

and S1903 supplies the actual determinant s1903ActualDeterminant l with

  average (s1903ActualDeterminant l) = -thetaLogVolume l / (M * card).

This file confronts the two sides of the resulting identity

  s1904ProcessionAverage (s1903ActualDeterminant l) = s1915A0 T

by computing both sides from the actual data, and identifies the exact
remaining arithmetic statement.  No equality is assumed or faked.

## What is proved here (all with the actual objects)

1. [PROVED] **The root-image radius is the actual root norm.**  For every bad
   place b,

     rootImageRadius T b = norm(root_b),

   where root_b = rootNormedElement T b is the actual 2l-th root of the
   actual qVFamily parameter.  This is the term-by-term relation which replaces
   the (false) guess "rootImageRadius T b = thetaScale l j": the hull radii are
   built from the *actual* local q_v, not from the paper real model thetaScale
   with q = 1/5.

2. [PROVED] **The exact closed form of a0.**  Combining 1. with
   rootNormedElementNorm_pow_twoL (norm(root_b)^(2l) = norm(qVFamily.q)) gives

     s1915ClosedForm T = 1 + (1/(2l)) * sum_b d_b * log(norm q_b),

   with d_b = [K_b : Q_p] the local degree and q_b the actual qVFamily
   parameter at b; hence a0 T = max 0 (that).

3. [PROVED] **The exact value of the actual determinant average.**

     average (s1903ActualDeterminant l) = log 5 * (sum_j j^2) / l^4

   (the sum over the signed labels), i.e. a pure rational multiple of log 5; it
   is positive.  Combined with 2., the bridge at the actual pair is equivalent
   to the single real equation

     2l + sum_b d_b * log(norm q_b) = 2l * (log 5 * sum_j j^2 / l^4)

   (s1928_identity_iff_scaled), the *exact first missing*.

4. [PROVED] **The structural obstruction.**  The two sides are of different
   kinds: the theta side is 1 plus a sum of logarithms of the actual local
   q_v-unit norms at the bad places, while the determinant side is a rational
   multiple of log 5 with zero rational part.  Consequently the identity is not
   a bookkeeping identity of the two normalizations: it is a genuine arithmetic
   identification of log 5 with the local q_v data
   (s1928_identity_iff_log_five).  The present definitions cannot prove it, and
   no choice of the free data removes it.

5. [PROVED] a0 T < 1 (the hull is a proper part of the scaled unit region)
   and 0 < average (s1903ActualDeterminant l).

6. [PROVED] **Unconditional failure on the clipped region.**  Wherever the
   S1915 unclipped closed form is nonpositive, a0 = 0 (S1915) while the actual
   average is positive, so the bridge is *false* there
   (s1928_bridge_false_of_closedForm_nonpos); no transcendence input is used.
   The complementary region is exactly where the arithmetic identity has to
   hold (s1928_closedForm_pos_of_bridge).

## Mathematical boundary of the identity (not formalized here)

Write norm(q_b) = p_b^(-e_b/f_b) with p_b the residue characteristic of the
place (a rational prime), e_b >= 1, f_b >= 1.  Then 3. reads

  2l = (2 * (sum_j j^2) / l^3) * log 5 + sum_b d_b * (e_b/f_b) * log p_b.

Exponentiating turns this into an equation of algebraic real numbers:

  exp (2l) = 5 ^ (2 * (sum_j j^2) / l^3) * prod_b p_b ^ (d_b * e_b/f_b).

The right-hand side is algebraic over Q (positive rational powers and finite
products of algebraic numbers are algebraic), while 2l != 0 is algebraic and
nonzero, so Lindemann-Weierstrass makes exp (2l) transcendental.  Hence the
identity is *false* for the actual pair, and a fortiori the S1904 bridge fails
there.  Nothing in Mathlib currently proves either the local norm formula
norm(q_b) = p_b^(-e_b/f_b) or Lindemann-Weierstrass, so this file does not
assert the refutation; it proves the exact reduction and records the missing
arithmetic as S1928ArithmeticIdentity / S1928FirstMissing.

Consumers: S1905Unconditional312Actual (s1928_s1905FirstMissing_iff), the S1880
D third field.

No sorry, axiom, True/PUnit slot, or arbitrary datum is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1928BridgeAverageA0Actual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1903SignedHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1905Unconditional312Actual
open LeanFormal.IUT.XiFPaperThetaHull
open MeasureTheory
open scoped BigOperators Pointwise

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 0. The label with representative one -/

/-- lStar l.value >= 1 for every prime l >= 5. -/
theorem s1928_one_le_lStar (l : PrimeGeFive) : 1 <= lStar l.value := by
  have h5 : 5 <= l.value := l.ge_five
  unfold lStar
  omega

/-- The signed label with representative 1. -/
def s1928LabelOne (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨1, by
    constructor
    · have h0 : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · exact_mod_cast s1928_one_le_lStar l⟩

@[simp] theorem s1928LabelOne_val (l : PrimeGeFive) : (s1928LabelOne l).1 = 1 := rfl

theorem s1928LabelOne_pos (l : PrimeGeFive) : 0 < (s1928LabelOne l).1 := by
  rw [s1928LabelOne_val]
  norm_num

/-! ## 1. The root norm and the actual image radius -/

/-- The actual root norm rho_b = norm(root_b) of the local root extension. -/
noncomputable def s1928RootNorm (b : Bad (nativePlaceSelection T)) : Real :=
  ‖rootNormedElement T b‖

theorem s1928RootNorm_pos (b : Bad (nativePlaceSelection T)) :
    0 < s1928RootNorm T b := by
  rw [s1928RootNorm, norm_pos_iff]
  exact rootNormedElement_ne_zero (T := T) (b := b)

theorem s1928RootNorm_le_one (b : Bad (nativePlaceSelection T)) :
    s1928RootNorm T b <= 1 :=
  rootNormedElement_norm_le_one (T := T) (b := b) (rootQUnitNormLeOne (T := T))

/-- The actual root norm is strictly below one. -/
theorem s1928RootNorm_lt_one (b : Bad (nativePlaceSelection T)) :
    s1928RootNorm T b < 1 :=
  rootNormedElement_norm_lt_one (T := T) (b := b)

/-- The norm of the label-j paper theta value is rho_b ^ (j^2). -/
theorem s1928RootNorm_pow (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      s1928RootNorm T b ^ gaussExponent j.1 :=
  rootNormedThetaValueInL_norm T b j

/-- The (2l)-th power of the root norm is the actual qVFamily parameter norm. -/
theorem s1928RootNorm_pow_twoL (b : Bad (nativePlaceSelection T)) :
    s1928RootNorm T b ^ (2 * l.value) =
      ‖(sourceRootQUnit T b : rootBase T b)‖ :=
  rootNormedElementNorm_pow_twoL T b

/-- ((2 * l.value : Nat) : Real) = 2 * l.value. -/
theorem s1928_cast_two_mul_l :
    ((2 * l.value : Nat) : Real) = 2 * (l.value : Real) := by
  push_cast
  ring

/-- **The actual image radius is the actual root norm.**  The coordinatewise
maximal root Theta norm is attained at the label j = 1, because every other
label has j^2 >= 1 and the root norm is at most one. -/
theorem s1928_rootImageRadius_eq_rootNorm (b : Bad (nativePlaceSelection T)) :
    (rootImageRadius T b : Real) = s1928RootNorm T b := by
  have hR0 : 0 <= s1928RootNorm T b := (s1928RootNorm_pos T b).le
  have hR1 : s1928RootNorm T b <= 1 := s1928RootNorm_le_one T b
  have hle : rootImageRadius T b <= ⟨s1928RootNorm T b, hR0⟩ := by
    unfold rootImageRadius
    refine Finset.sup_le (fun j _ => ?_)
    have hj1 : (1 : Int) <= (j.1).1 := by
      have := j.2
      omega
    have hsq : (1 : Int) <= gaussExponent (j.1).1 := by
      unfold gaussExponent
      have h := mul_le_mul hj1 hj1
        (by norm_num : (0 : Int) <= 1)
        (by omega : (0 : Int) <= (j.1).1)
      simpa [pow_two] using h
    have hz := zpow_le_zpow_right_of_le_one₀ (s1928RootNorm_pos T b) hR1 hsq
    have hreal : ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)‖ <= s1928RootNorm T b := by
      change ‖(rootNormedThetaValueInL T b (j.1) : rootNormedExtension T b)‖ <=
        s1928RootNorm T b
      rw [s1928RootNorm_pow]
      simpa using hz
    exact hreal
  have hge : (⟨s1928RootNorm T b, hR0⟩ : NNReal) <= rootImageRadius T b := by
    have hreal : ‖(rootNormedThetaValueInL T b
          (thetaLabelToSigned (l := l)
            (⟨s1928LabelOne l, s1928LabelOne_pos l⟩ : ThetaLabel (l := l))) :
          rootNormedExtension T b)‖ = s1928RootNorm T b := by
      change ‖(rootNormedThetaValueInL T b (s1928LabelOne l) :
        rootNormedExtension T b)‖ = s1928RootNorm T b
      rw [s1928RootNorm_pow]
      have hg : gaussExponent (s1928LabelOne l).1 = 1 := by
        rw [s1928LabelOne_val]
        unfold gaussExponent
        norm_num
      rw [hg, zpow_one]
    have hval : (⟨‖(rootNormedThetaValueInL T b
          (thetaLabelToSigned (l := l)
            (⟨s1928LabelOne l, s1928LabelOne_pos l⟩ : ThetaLabel (l := l))) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal) =
        ⟨s1928RootNorm T b, hR0⟩ := by
      exact Subtype.ext hreal
    rw [← hval]
    unfold rootImageRadius
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j : ThetaLabel (l := l) =>
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal))
      (b := (⟨s1928LabelOne l, s1928LabelOne_pos l⟩ : ThetaLabel (l := l)))
      (Finset.mem_univ _)
  have heq : rootImageRadius T b = ⟨s1928RootNorm T b, hR0⟩ := le_antisymm hle hge
  rw [heq]
  rfl

/-- The logarithm of the actual root norm is the normalized logarithm of the
actual qVFamily parameter norm. -/
theorem s1928_log_rootNorm (b : Bad (nativePlaceSelection T)) :
    Real.log (s1928RootNorm T b) =
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ / (2 * (l.value : Real)) := by
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have h2l : (2 * (l.value : Real)) ≠ 0 := by positivity
  have hlog : Real.log (s1928RootNorm T b ^ (2 * l.value)) =
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
    rw [s1928RootNorm_pow_twoL]
  rw [Real.log_pow, s1928_cast_two_mul_l] at hlog
  rw [eq_div_iff h2l]
  linarith

/-- **The exact closed form of the S1915 a0** in terms of the actual local
qVFamily parameters. -/
theorem s1928_closedForm_eq :
    s1915ClosedForm T =
      1 + (1 / (2 * (l.value : Real))) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) *
            Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
  unfold s1915ClosedForm
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [s1928_rootImageRadius_eq_rootNorm (T := T) b]
  rw [s1928_log_rootNorm (T := T) b]
  ring

/-! ## 2. The actual determinant average -/

/-- The paper real model q = 1/5 has log -log 5. -/
theorem s1928_log_gaussianFiveThetaQ :
    Real.log gaussianFiveThetaQ = -Real.log 5 := by
  rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five,
    Real.log_inv]

/-- The actual theta log-scale at a label is -j^2 log 5. -/
theorem s1928_thetaLogScale_eq (j : SignedLabel l.value) :
    thetaLogScale l j = -((j.1 : Real) ^ 2) * Real.log 5 := by
  rw [theta_log_scale_eq, s1928_log_gaussianFiveThetaQ]
  have hcast : ((gaussExponent j.1).toNat : Real) = (j.1 : Real) ^ 2 := by
    rw [← Int.cast_natCast,
      Int.toNat_of_nonneg (by unfold gaussExponent; exact sq_nonneg j.1)]
    unfold gaussExponent
    push_cast
    ring
  rw [hcast]
  ring

/-- The actual theta log-volume is -log 5 times the sum of the squared labels. -/
theorem s1928_thetaLogVolume_eq :
    thetaLogVolume l = -Real.log 5 * (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) := by
  rw [theta_log_volume_eq_sum]
  calc (∑ j : SignedLabel l.value, thetaLogScale l j)
      = ∑ j : SignedLabel l.value, (-((j.1 : Real) ^ 2) * Real.log 5) :=
        Finset.sum_congr rfl (fun j _ => s1928_thetaLogScale_eq j)
    _ = -Real.log 5 * (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) := by
        have hstep : (∑ j : SignedLabel l.value, (-((j.1 : Real) ^ 2) * Real.log 5)) =
            (∑ j : SignedLabel l.value, ((j.1 : Real) ^ 2) * (-Real.log 5)) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [hstep, ← Finset.sum_mul]
        ring

/-- **The exact value of the actual determinant procession average**:
log 5 * (sum of the squared labels) / l^4. -/
theorem s1928_average_eq :
    s1904ProcessionAverage (s1903ActualDeterminant l) =
      Real.log 5 * (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) /
        ((l.value : Real) ^ 4) := by
  have hcard : Fintype.card (SignedLabel l.value) = l.value :=
    SignedLabel.card_signedLabel l
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have hbase := s1903RootProcession_average l (s1903TensorPower l)
    (s1903TensorPower_ne_zero l)
  show (s1903ActualDeterminant l).procession.average = _
  rw [show (s1903ActualDeterminant l).procession =
      s1903RootProcession l (s1903TensorPower l) from rfl]
  rw [hbase, s1928_thetaLogVolume_eq, hcard]
  unfold s1903TensorPower
  rw [hcard]
  push_cast
  field_simp

/-- The squared-label sum is positive. -/
theorem s1928_sum_sq_pos :
    0 < (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) := by
  refine Finset.sum_pos' (fun j _ => by positivity) ?_
  refine ⟨s1928LabelOne l, Finset.mem_univ _, ?_⟩
  rw [s1928LabelOne_val]
  norm_num

/-- The actual determinant procession average is positive. -/
theorem s1928_average_pos : 0 < s1904ProcessionAverage (s1903ActualDeterminant l) := by
  rw [s1928_average_eq]
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  exact div_pos (mul_pos hlog s1928_sum_sq_pos) (by positivity)

/-! ## 3. Strictness: the hull is a proper part of the scaled unit region -/

/-- The bad-place set is nonempty. -/
theorem s1928_bad_nonempty : Nonempty (Bad (nativePlaceSelection T)) := by
  obtain ⟨p, hp⟩ := nativePlaceSelection_nonempty T
  exact ⟨⟨p, hp⟩⟩

/-- The local degree is positive. -/
theorem s1928_localDegree_pos (b : Bad (nativePlaceSelection T)) :
    0 < s1915LocalDegree T b := by
  unfold s1915LocalDegree
  exact Module.finrank_pos

/-- The logarithm of the actual local qVFamily parameter norm is negative. -/
theorem s1928_log_q_neg (b : Bad (nativePlaceSelection T)) :
    Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ < 0 := by
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have h2l : (0 : Real) < 2 * (l.value : Real) := by linarith
  have hR : Real.log (s1928RootNorm T b) < 0 :=
    Real.log_neg (s1928RootNorm_pos T b) (s1928RootNorm_lt_one T b)
  have hlog : Real.log (s1928RootNorm T b ^ (2 * l.value)) =
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
    rw [s1928RootNorm_pow_twoL]
  rw [Real.log_pow, s1928_cast_two_mul_l] at hlog
  rw [← hlog]
  exact mul_neg_of_pos_of_neg h2l hR

/-- The local qVFamily log-sum is negative. -/
theorem s1928_local_sum_neg :
    (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) < 0 := by
  have hneg : ∀ b ∈ (Finset.univ : Finset (Bad (nativePlaceSelection T))),
      0 < (s1915LocalDegree T b : Real) *
        (-Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) := by
    intro b _
    have hd : (0 : Real) < (s1915LocalDegree T b : Real) := by
      exact_mod_cast s1928_localDegree_pos T b
    have hq : 0 < -Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ :=
      neg_pos.mpr (s1928_log_q_neg T b)
    exact mul_pos hd hq
  haveI hne : Nonempty (Bad (nativePlaceSelection T)) := s1928_bad_nonempty T
  have hpos : 0 < (∑ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) *
        (-Real.log ‖(sourceRootQUnit T b : rootBase T b)‖)) :=
    Finset.sum_pos hneg Finset.univ_nonempty
  have hsplit : (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) =
      -(∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          (-Real.log ‖(sourceRootQUnit T b : rootBase T b)‖)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsplit]
  linarith

/-- The unclipped closed form is strictly below one: the actual hull is a
proper part of the scaled unit region. -/
theorem s1928_closedForm_lt_one : s1915ClosedForm T < 1 := by
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have hone : (0 : Real) < 1 / (2 * (l.value : Real)) := by positivity
  have h := s1928_closedForm_eq (T := T)
  rw [h]
  have hterm : (1 / (2 * (l.value : Real))) *
      (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) < 0 :=
    mul_neg_of_pos_of_neg hone (s1928_local_sum_neg T)
  linarith

/-- The actual value a0 is strictly below one. -/
theorem s1928_a0_lt_one : s1915A0 T < 1 := by
  rw [s1915_a0_eq_max, max_lt_iff]
  exact ⟨by norm_num, s1928_closedForm_lt_one T⟩

/-! ## 4. The bridge is exactly the arithmetic identity -/

/-- The exact arithmetic identity behind the S1904 bridge at the actual
S1902/S1903 fields: the unclipped closed form of a0 equals the actual
determinant procession average. -/
def S1928ArithmeticIdentity : Prop :=
  s1915ClosedForm T = s1904ProcessionAverage (s1903ActualDeterminant l)

/-- The exact first missing proposition at the actual fields. -/
def S1928FirstMissing : Prop :=
  S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l)

/-- The first missing proposition is the S1904 bridge at the actual fields. -/
theorem s1928_firstMissing_iff_bridge :
    S1928FirstMissing T ↔
      S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) :=
  Iff.rfl

/-- A positive right-hand side makes max 0 x = y equivalent to x = y. -/
theorem s1928_max_eq_iff {x y : Real} (hy : 0 < y) : max 0 x = y ↔ x = y := by
  constructor
  · intro h
    by_cases hx : 0 <= x
    · rwa [max_eq_right hx] at h
    · rw [max_eq_left (le_of_lt (not_le.mp hx))] at h
      linarith
  · intro h
    rw [h]
    exact max_eq_right hy.le

/-- The S1904 bridge at the actual fields, read as average = a0 (S1915). -/
theorem s1928_bridge_iff_average_eq :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) ↔
      s1904ProcessionAverage (s1903ActualDeterminant l) = s1915A0 T :=
  s1915_bridge_iff_average_eq_a0 T _

/-- **The S1904 bridge at the actual S1902 hull and the actual S1903
determinant is exactly the arithmetic identity.** -/
theorem s1928_bridge_iff_identity :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) ↔
      S1928ArithmeticIdentity T := by
  rw [s1928_bridge_iff_average_eq, s1915_a0_eq_max]
  constructor
  · intro h
    exact (s1928_max_eq_iff s1928_average_pos).mp h.symm
  · intro h
    exact ((s1928_max_eq_iff s1928_average_pos).mpr h).symm

/-- The exact first missing is the arithmetic identity. -/
theorem s1928_firstMissing_iff_identity :
    S1928FirstMissing T ↔ S1928ArithmeticIdentity T :=
  s1928_bridge_iff_identity T

/-- The arithmetic identity in fully explicit form: 1 plus the normalized
sum of the logarithms of the actual local qVFamily parameter norms equals the
rational multiple of log 5 coming from the actual theta packet. -/
theorem s1928_identity_explicit (h : S1928ArithmeticIdentity T) :
    1 + (1 / (2 * (l.value : Real))) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) *
            Real.log ‖(sourceRootQUnit T b : rootBase T b)‖
      = Real.log 5 * (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) /
          ((l.value : Real) ^ 4) := by
  rw [S1928ArithmeticIdentity, s1928_closedForm_eq, s1928_average_eq] at h
  exact h

/-- The scaled explicit form of the identity: 2l plus the local qVFamily
log-sum equals the rational multiple of log 5. -/
theorem s1928_identity_iff_scaled :
    S1928ArithmeticIdentity T ↔
      2 * (l.value : Real) +
          ∑ b : Bad (nativePlaceSelection T),
            (s1915LocalDegree T b : Real) *
              Real.log ‖(sourceRootQUnit T b : rootBase T b)‖
        = 2 * (l.value : Real) * Real.log 5 *
            (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) / ((l.value : Real) ^ 4) := by
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have h2l : (2 * (l.value : Real)) ≠ 0 := by positivity
  rw [S1928ArithmeticIdentity, s1928_closedForm_eq, s1928_average_eq]
  have key : 1 + (1 / (2 * (l.value : Real))) *
      (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) =
      (2 * (l.value : Real) +
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) *
            Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) /
        (2 * (l.value : Real)) := by
    field_simp
  rw [key, div_eq_iff h2l]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [h]
    ring

/-- The identity is a genuine identification of log 5 with the actual local
qVFamily data: it determines log 5 by the arithmetic of the bad places. -/
theorem s1928_identity_iff_log_five :
    S1928ArithmeticIdentity T ↔
      Real.log 5 =
        (2 * (l.value : Real) +
            ∑ b : Bad (nativePlaceSelection T),
              (s1915LocalDegree T b : Real) *
                Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) /
          (2 * (l.value : Real) * (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) /
            ((l.value : Real) ^ 4)) := by
  rw [s1928_identity_iff_scaled]
  have hl0 : (0 : Real) < l.value := by exact_mod_cast l.prime.pos
  have hS : (0 : Real) < ∑ j : SignedLabel l.value, (j.1 : Real) ^ 2 :=
    s1928_sum_sq_pos
  have hden : (2 * (l.value : Real) *
      (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) / ((l.value : Real) ^ 4)) ≠ 0 := by
    positivity
  constructor
  · intro h
    rw [eq_div_iff hden, h]
    ring
  · intro h
    rw [eq_div_iff hden] at h
    rw [← h]
    ring

/-! ## 4b. Unconditional failure on the clipped region a0 = 0 -/

/-- **The bridge fails whenever the S1915 value a0 is zero.**  In that region
the theta side is the rational number zero, while the actual determinant
average is strictly positive; no transcendence input is needed. -/
theorem s1928_bridge_false_of_a0_eq_zero (h : s1915A0 T = 0) :
    ¬ S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) := by
  intro hb
  have havg : s1904ProcessionAverage (s1903ActualDeterminant l) = 0 := by
    rw [s1928_bridge_iff_average_eq] at hb
    rw [hb, h]
  exact (ne_of_gt s1928_average_pos) havg

/-- **The bridge fails on the whole clipped region s1915ClosedForm T <= 0**:
there a0 = 0 (S1915) while the actual determinant average is positive. -/
theorem s1928_bridge_false_of_closedForm_nonpos (h : s1915ClosedForm T <= 0) :
    ¬ S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) :=
  s1928_bridge_false_of_a0_eq_zero T (s1915_a0_eq_zero_of_closedForm_nonpos T h)

/-- The complementary region: a bridge would force the unclipped closed form to
be the positive average, i.e. it would force s1915ClosedForm T > 0. -/
theorem s1928_closedForm_pos_of_bridge
    (hb : S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l)) :
    0 < s1915ClosedForm T := by
  rw [s1928_bridge_iff_identity] at hb
  rw [S1928ArithmeticIdentity] at hb
  rw [hb]
  exact s1928_average_pos

/-! ## 5. The S1905 first missing -/

/-- **The S1905 first missing is exactly the arithmetic identity at the actual
S1902/S1903 fields.** -/
theorem s1928_s1905FirstMissing_iff :
    S1905FirstMissing T ↔ S1928ArithmeticIdentity T :=
  s1928_firstMissing_iff_identity T

/-- **The S1905 first missing in explicit arithmetic form**: it is the single
real equation between the actual local qVFamily log-sum and log 5. -/
theorem s1928_s1905FirstMissing_iff_scaled :
    S1905FirstMissing T ↔
      2 * (l.value : Real) +
          ∑ b : Bad (nativePlaceSelection T),
            (s1915LocalDegree T b : Real) *
              Real.log ‖(sourceRootQUnit T b : rootBase T b)‖
        = 2 * (l.value : Real) * Real.log 5 *
            (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) / ((l.value : Real) ^ 4) :=
  (s1928_firstMissing_iff_identity T).trans (s1928_identity_iff_scaled T)

/-! ## 6. Axiom probes -/

#print axioms s1928_rootImageRadius_eq_rootNorm
#print axioms s1928_log_rootNorm
#print axioms s1928_closedForm_eq
#print axioms s1928_thetaLogVolume_eq
#print axioms s1928_average_eq
#print axioms s1928_average_pos
#print axioms s1928_closedForm_lt_one
#print axioms s1928_a0_lt_one
#print axioms s1928_bridge_iff_identity
#print axioms s1928_identity_explicit
#print axioms s1928_identity_iff_scaled
#print axioms s1928_bridge_false_of_closedForm_nonpos
#print axioms s1928_closedForm_pos_of_bridge
#print axioms s1928_s1905FirstMissing_iff

end LeanFormal.IUT.XiFPaper.S1928BridgeAverageA0Actual

end
