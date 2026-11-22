import tmp.sheaf.xif.paper.S1928BridgeAverageA0Actual
import tmp.sheaf.xif.paper.S1930CompareA0AverageActual

/-!
# S1939: the actual root-packet determinant of Corollary 3.12

Layer: **O** (original-text Theta-link / Step (xi-f), Corollary 3.12).

## Why the S1903 determinant is not the source determinant

S1903 built the determinant from the paper *real model* theta packet

  thetaScale l j = q ^ (j ^ 2),   q = gaussianFiveThetaQ = 1/5,

and S1928/S1930 computed its procession average

  average (s1903ActualDeterminant l) = log 5 * (l ^ 2 - 1) / (12 * l ^ 3),

a pure rational multiple of log 5.  S1928 proved that the S1904 procession
bridge at the actual S1902 hull is equivalent to a genuine arithmetic
identity between log 5 and the actual local qVFamily log-norms, and that this
identity fails on the clipped region.  S1928/S1930 state the correction: the
source determinant must be built from the **actual root packet**
(rootNormedThetaValueInL, equivalently the root radii ||rootNormedElement|| /
singleLambda) with the actual local degrees, and normalized so that its
procession average is the actual S1915 Haar readout a0.

## What is constructed here (no fake log-volume)

For every bad place b and every signed label j let

  L_j(b) = log ||rootNormedThetaValueInL T b j||,

the actual local log-magnitude of the paper Theta value root_b ^ (j ^ 2) in
the actual root extension rootNormedExtension T b (S201 proves
||root_b ^ (j^2)|| = ||root_b|| ^ (j^2)).  Define the packet log-scale

  s1939RootLogScale j = 1 + (1 / M) * sum_b [K_b : Q_p] * L_j(b),

with M = l * (l + 1) / 12, the paper j-normalization (the S694 mean square
(1/l*) sum_{j=1}^{l*} j^2, l* = (l-1)/2).  The 1 is the archimedean
e-normalization of the paper packet normalization (Remark 3.9.5(i)); the
divisor M is the j-normalization.

The determinant is the actual root packet

  hullPacket.scale j = exp (s1939RootLogScale j),

with unit reference packet, tensor power 1, and the **paper l* procession**:
weight 1/l* on each positive label j = 1, ..., l*, zero on 0 and on the
negative labels.

## The exact identities (proved)

1. s1939LabelLog_eq: the total actual local log-magnitude at label j is
   j^2 * S, where S = s1939BadLog T = sum_b [K_b : Q_p] log ||root_b||.
   Hence the packet is built from the actual root packet and the actual local
   degrees, not from thetaScale/gaussianFiveThetaQ.

2. s1939_average_eq_closedForm (unconditional): the l*-procession average of
   the actual root packet is **exactly** the unclipped S1915 closed form

     average = 1 + S = s1915ClosedForm T.

   The proof is the Gaussian mean-square identity
   sum_{j=1}^{l*} j^2 = l* * M, so the j-normalization cancels the j^2
   factors of the procession.  This is the actual-root-packet replacement of
   the log 5 model of S1928.

3. s1939_hullScaleBound_iff: the packet is a genuine hull packet (every scale
   at least one) **iff** the explicit real inequality

     S1939HullScaleBound : (l*)^2 * |S| <= M.

   Thus the only missing input of the construction is this concrete
   inequality on the actual local qVFamily data; there is no transcendence
   identity and no log 5.

4. s1939_average_eq_a0, s1939_bridge: under the scale bound the procession
   average is s1915A0 T and the S1904 procession bridge holds at the actual
   S1902 hull and the actual root-packet determinant.  Hence the paper
   signed-hull datum OrigXiFPaperSignedHullData is inhabited, and S1880 gives
   the Corollary 3.12 inequality

     -|log q| <= -|log Theta|

   at the actual root-packet determinant.

5. s1939Determinant_hullLogVolume: the determinant hull log-volume is
   l + (l - 1) * S, so the determinant is not a hand-supplied real but the
   actual packet log-volume (tensor power one, unit reference).

6. s1939_exists_bridge_iff_hullScaleBound: for any SignedHullLogActual with
   exactly this actual root packet and this paper l* procession, the S1904
   bridge at the actual S1902 hull exists iff the hull-scale bound holds.
   This is the precise first missing.

No sorry, axiom, True/PUnit slot, free real parameter, or fake log-volume is
used.  The only unproved input is the named real inequality above.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1939RootPacketDeterminantActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1903SignedHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1928BridgeAverageA0Actual
open LeanFormal.IUT.XiFPaper.S1930CompareA0AverageActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S1880OriginalXiFActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open scoped BigOperators

universe u

local instance s1939GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1939FivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The actual root packet and the paper j-normalization -/

noncomputable def s1939MeanSquare (l : PrimeGeFive) : Real :=
  (l.value : Real) * ((l.value : Real) + 1) / 12

theorem s1939MeanSquare_pos (l : PrimeGeFive) : 0 < s1939MeanSquare l := by
  unfold s1939MeanSquare
  have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  positivity

theorem s1939MeanSquare_ne_zero (l : PrimeGeFive) : s1939MeanSquare l ≠ 0 :=
  ne_of_gt (s1939MeanSquare_pos l)

noncomputable def s1939RootLog (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : Real :=
  Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖

noncomputable def s1939LabelLog (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * s1939RootLog T b j

noncomputable def s1939BadLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b)

noncomputable def s1939RootLogScale (j : SignedLabel l.value) : Real :=
  1 + s1939LabelLog T j / s1939MeanSquare l

noncomputable def s1939RootPacket :
    PositivePacket (SignedLabel l.value) where
  scale j := Real.exp (s1939RootLogScale T j)
  positive _ := Real.exp_pos _

noncomputable def s1939Weight (j : SignedLabel l.value) : Real :=
  if 0 < j.1 then ((lStar l.value : Real))⁻¹ else 0

/-! ## 2. The actual label log-magnitude is j^2 * S -/

theorem s1939_gaussExponent_cast (j : SignedLabel l.value) :
    ((gaussExponent j.1 : Int) : Real) = (j.1 : Real) ^ 2 := by
  unfold gaussExponent
  push_cast
  ring

theorem s1939RootLog_eq (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    s1939RootLog T b j =
      (j.1 : Real) ^ 2 * Real.log (s1928RootNorm T b) := by
  unfold s1939RootLog
  rw [s1928RootNorm_pow (T := T) (b := b) (j := j)]
  rw [Real.log_zpow, s1939_gaussExponent_cast]

theorem s1939LabelLog_eq (j : SignedLabel l.value) :
    s1939LabelLog T j = (j.1 : Real) ^ 2 * s1939BadLog T := by
  unfold s1939LabelLog s1939BadLog
  calc
    (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * s1939RootLog T b j)
        = ∑ b : Bad (nativePlaceSelection T),
            (s1915LocalDegree T b : Real) *
              ((j.1 : Real) ^ 2 * Real.log (s1928RootNorm T b)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [s1939RootLog_eq]
    _ = ∑ b : Bad (nativePlaceSelection T),
            (j.1 : Real) ^ 2 *
              ((s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = (j.1 : Real) ^ 2 *
          ∑ b : Bad (nativePlaceSelection T),
            (s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b) := by
          rw [Finset.mul_sum]

/-! ## 3. The Gaussian mean-square identities -/

theorem s1939_lStar_eq (l : PrimeGeFive) :
    (lStar l.value : Real) = ((l.value : Real) - 1) / 2 := by
  have h := s1930_two_mul_lStar_add_one l
  have hR : (2 * (lStar l.value : Real) + 1) = (l.value : Real) := by
    exact_mod_cast h
  linarith

theorem s1939PositiveLabel_sq (i : Fin (lStar l.value)) :
    ((s1930PositiveLabel l i).1 : Real) ^ 2 = ((i.1 : Real) + 1) ^ 2 := by
  rw [s1930PositiveLabel_val]
  push_cast
  ring

theorem s1939_sum_sq_positive_eq :
    (∑ i : Fin (lStar l.value),
        ((s1930PositiveLabel l i).1 : Real) ^ 2)
      = (l.value : Real) * ((l.value : Real) ^ 2 - 1) / 24 := by
  calc
    (∑ i : Fin (lStar l.value),
        ((s1930PositiveLabel l i).1 : Real) ^ 2)
        = ∑ i : Fin (lStar l.value), ((i.1 : Real) + 1) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [s1939PositiveLabel_sq]
    _ = (l.value : Real) * ((l.value : Real) ^ 2 - 1) / 24 :=
          s1930_sum_sq_paperLabel l

theorem s1939_sum_sq_positive_eq_mean :
    (∑ i : Fin (lStar l.value),
        ((s1930PositiveLabel l i).1 : Real) ^ 2)
      = (lStar l.value : Real) * s1939MeanSquare l := by
  rw [s1939_sum_sq_positive_eq]
  unfold s1939MeanSquare
  rw [s1939_lStar_eq l]
  field_simp
  ring

theorem s1939_positiveFilter_sum_sq :
    (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)),
        (j.1 : Real) ^ 2) = (lStar l.value : Real) * s1939MeanSquare l := by
  rw [s1930PositiveFilter_sum_eq l (fun j : SignedLabel l.value => (j.1 : Real) ^ 2)]
  exact s1939_sum_sq_positive_eq_mean

theorem s1939_positiveFilter_card :
    (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)).card =
      lStar l.value := by
  have h := s1930PositiveFilter_sum_eq l
    (fun _ : SignedLabel l.value => (1 : Real))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_fin] at h
  exact_mod_cast h

theorem s1939_lStar_ne_zero (l : PrimeGeFive) : (lStar l.value : Real) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (s1930_lStar_pos l))

/-! ## 4. The paper l* procession -/

theorem s1939Weight_sum_eq_one :
    (∑ j : SignedLabel l.value, s1939Weight j) = 1 := by
  unfold s1939Weight
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, s1939_positiveFilter_card]
  exact mul_inv_cancel₀ (s1939_lStar_ne_zero l)

noncomputable def s1939Procession : WeightedValues (SignedLabel l.value) where
  value j := s1939RootLogScale T j
  weight j := s1939Weight j
  weightTotal := 1
  weightTotal_pos := one_pos
  weightTotal_eq_sum := s1939Weight_sum_eq_one.symm

theorem s1939WeightedSum_eq :
    (∑ j : SignedLabel l.value, s1939Weight j * s1939RootLogScale T j)
      = 1 + s1939BadLog T := by
  have hM := s1939MeanSquare_ne_zero l
  have hstar := s1939_lStar_ne_zero l
  have hstep : (∑ j : SignedLabel l.value,
        s1939Weight j * s1939RootLogScale T j)
      = ∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)),
          (lStar l.value : Real)⁻¹ *
            (1 + s1939LabelLog T j / s1939MeanSquare l) := by
    unfold s1939Weight s1939RootLogScale
    have hcongr : ∀ j : SignedLabel l.value,
        (if 0 < j.1 then (lStar l.value : Real)⁻¹ else 0) *
            (1 + s1939LabelLog T j / s1939MeanSquare l) =
          if 0 < j.1 then
            (lStar l.value : Real)⁻¹ *
              (1 + s1939LabelLog T j / s1939MeanSquare l) else 0 := by
      intro j
      by_cases h : 0 < j.1 <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => hcongr j)]
    rw [← Finset.sum_filter]
  rw [hstep]
  rw [s1930PositiveFilter_sum_eq l
    (fun j : SignedLabel l.value =>
      (lStar l.value : Real)⁻¹ *
        (1 + s1939LabelLog T j / s1939MeanSquare l))]
  have hsum : (∑ i : Fin (lStar l.value),
        s1939LabelLog T (s1930PositiveLabel l i))
      = ((lStar l.value : Real) * s1939MeanSquare l) * s1939BadLog T := by
    calc
      (∑ i : Fin (lStar l.value),
          s1939LabelLog T (s1930PositiveLabel l i))
          = ∑ i : Fin (lStar l.value),
              ((s1930PositiveLabel l i).1 : Real) ^ 2 * s1939BadLog T := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [s1939LabelLog_eq]
      _ = ((∑ i : Fin (lStar l.value),
              ((s1930PositiveLabel l i).1 : Real) ^ 2)) * s1939BadLog T := by
            rw [Finset.sum_mul]
      _ = ((lStar l.value : Real) * s1939MeanSquare l) * s1939BadLog T := by
            rw [s1939_sum_sq_positive_eq_mean]
  have houter : (∑ i : Fin (lStar l.value),
        (lStar l.value : Real)⁻¹ *
          (1 + s1939LabelLog T (s1930PositiveLabel l i) /
            s1939MeanSquare l)) =
      (lStar l.value : Real)⁻¹ *
        ∑ i : Fin (lStar l.value),
          (1 + s1939LabelLog T (s1930PositiveLabel l i) /
            s1939MeanSquare l) := by
    rw [Finset.mul_sum]
  rw [houter]
  have hinner : (∑ i : Fin (lStar l.value),
        (1 + s1939LabelLog T (s1930PositiveLabel l i) /
          s1939MeanSquare l)) =
      (lStar l.value : Real) +
        ((lStar l.value : Real) * s1939MeanSquare l) *
          s1939BadLog T / s1939MeanSquare l := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    have hones : (∑ i : Fin (lStar l.value), (1 : Real)) =
        (lStar l.value : Real) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp
    rw [hones, hsum]
  rw [hinner]
  field_simp [hstar, hM]

theorem s1939BadLog_eq :
    s1939BadLog T =
      (1 / (2 * (l.value : Real))) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) *
            Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
  unfold s1939BadLog
  calc
    (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log (s1928RootNorm T b))
        = ∑ b : Bad (nativePlaceSelection T),
            (s1915LocalDegree T b : Real) *
              (Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ /
                (2 * (l.value : Real))) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [s1928_log_rootNorm]
    _ = ∑ b : Bad (nativePlaceSelection T),
            (1 / (2 * (l.value : Real))) *
              ((s1915LocalDegree T b : Real) *
                Real.log ‖(sourceRootQUnit T b : rootBase T b)‖) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = (1 / (2 * (l.value : Real))) *
          ∑ b : Bad (nativePlaceSelection T),
            (s1915LocalDegree T b : Real) *
              Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
          rw [Finset.mul_sum]

theorem s1939BadLog_neg : s1939BadLog T < 0 := by
  rw [s1939BadLog_eq]
  have hl : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
  have hcoef : (0 : Real) < 1 / (2 * (l.value : Real)) := by positivity
  exact mul_neg_of_pos_of_neg hcoef (s1928_local_sum_neg T)

theorem s1939_closedForm_eq_badLog :
    s1915ClosedForm T = 1 + s1939BadLog T := by
  rw [s1928_closedForm_eq, ← s1939BadLog_eq]

theorem s1939_average_eq_closedForm :
    (s1939Procession T).average = s1915ClosedForm T := by
  unfold WeightedValues.average
  change (∑ j : SignedLabel l.value, s1939Weight j * s1939RootLogScale T j) /
      (1 : Real) = s1915ClosedForm T
  rw [div_one, s1939WeightedSum_eq]
  exact (s1939_closedForm_eq_badLog T).symm

/-! ## 5. The hull-scale bound: the precise first missing -/

/-- The only input needed to make the actual root packet a genuine hull packet:
the largest positive-label log-scale is nonnegative, i.e.
(l*)^2 * |S| <= M. -/
def s1939HullScaleBound : Prop :=
  (lStar l.value : Real) ^ 2 * |s1939BadLog T| <= s1939MeanSquare l

theorem s1939_absBadLog_lt_one (h : s1939HullScaleBound T) :
    |s1939BadLog T| < 1 := by
  have hM := s1939MeanSquare_pos l
  have h5 : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hls : (1 : Real) <= (lStar l.value : Real) := by
    rw [s1939_lStar_eq l]
    linarith
  have hls0 : (0 : Real) < (lStar l.value : Real) := by linarith
  have hls2 : (0 : Real) < (lStar l.value : Real) ^ 2 := pow_pos hls0 2
  unfold s1939HullScaleBound at h
  have hdiv : |s1939BadLog T| <= s1939MeanSquare l / (lStar l.value : Real) ^ 2 := by
    rw [le_div_iff₀ hls2]
    simpa only [mul_comm] using h
  have hlt : s1939MeanSquare l / (lStar l.value : Real) ^ 2 < 1 := by
    rw [div_lt_one hls2]
    unfold s1939MeanSquare
    rw [s1939_lStar_eq l]
    nlinarith
  linarith

theorem s1939_closedForm_pos (h : s1939HullScaleBound T) :
    0 < s1915ClosedForm T := by
  rw [s1939_closedForm_eq_badLog]
  have hS := s1939BadLog_neg T
  have hlt := s1939_absBadLog_lt_one T h
  have habs : |s1939BadLog T| = -s1939BadLog T := abs_of_neg hS
  linarith

theorem s1939_average_eq_a0 (h : s1939HullScaleBound T) :
    (s1939Procession T).average = s1915A0 T := by
  rw [s1939_average_eq_closedForm]
  exact (s1915_a0_eq_closedForm T (le_of_lt (s1939_closedForm_pos T h))).symm

/-- The unconditional average identity equals a0 exactly when the S1915
ENNReal clipping is inactive, i.e. |S| <= 1.  This is weaker than the
hull-scale bound, which is what the SignedHullLogActual structure needs. -/
theorem s1939_average_eq_a0_iff :
    (s1939Procession T).average = s1915A0 T ↔ |s1939BadLog T| <= 1 := by
  have hS := s1939BadLog_neg T
  have hSabs : |s1939BadLog T| = -s1939BadLog T := abs_of_neg hS
  rw [s1939_average_eq_closedForm, s1915_a0_eq_max, s1939_closedForm_eq_badLog]
  constructor
  · intro h
    have hnonneg : (0 : Real) <= 1 + s1939BadLog T := by
      rw [h]
      exact le_max_left 0 (1 + s1939BadLog T)
    rw [hSabs]
    linarith
  · intro h
    have hnonneg : (0 : Real) <= 1 + s1939BadLog T := by
      rw [hSabs] at h
      linarith
    rw [max_eq_right hnonneg]

theorem s1939_average_eq_a0_of_abs_le_one (h : |s1939BadLog T| <= 1) :
    (s1939Procession T).average = s1915A0 T :=
  (s1939_average_eq_a0_iff T).mpr h

@[simp] theorem s1939RootPacket_scale (j : SignedLabel l.value) :
    (s1939RootPacket T).scale j = Real.exp (s1939RootLogScale T j) := rfl

theorem s1939_hull_scales_ge_one (h : s1939HullScaleBound T) :
    ∀ j : SignedLabel l.value, 1 <= (s1939RootPacket T).scale j := by
  intro j
  rw [s1939RootPacket_scale, Real.one_le_exp_iff]
  have hM := s1939MeanSquare_pos l
  have hS := s1939BadLog_neg T
  have hls0 : (0 : Real) <= (lStar l.value : Real) := by
    have := s1930_lStar_pos l
    exact_mod_cast this.le
  have h1 : (j.1 : Real) <= (lStar l.value : Real) := by exact_mod_cast j.2.2
  have h2 : -(lStar l.value : Real) <= (j.1 : Real) := by exact_mod_cast j.2.1
  have hj : (j.1 : Real) ^ 2 <= (lStar l.value : Real) ^ 2 := by
    have hprod : 0 <= ((lStar l.value : Real) - (j.1 : Real)) *
        ((lStar l.value : Real) + (j.1 : Real)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hmul : (j.1 : Real) ^ 2 * |s1939BadLog T| <=
      (lStar l.value : Real) ^ 2 * |s1939BadLog T| :=
    mul_le_mul_of_nonneg_right hj (abs_nonneg _)
  have hle : (j.1 : Real) ^ 2 * |s1939BadLog T| <= s1939MeanSquare l :=
    le_trans hmul h
  have hSabs : s1939BadLog T = -|s1939BadLog T| := by
    linarith [abs_of_neg hS]
  rw [s1939RootLogScale, s1939LabelLog_eq, hSabs]
  have hEq : 1 + (j.1 : Real) ^ 2 * (-|s1939BadLog T|) / s1939MeanSquare l =
      1 - ((j.1 : Real) ^ 2 * |s1939BadLog T|) / s1939MeanSquare l := by
    ring
  rw [hEq]
  have hdiv : ((j.1 : Real) ^ 2 * |s1939BadLog T|) / s1939MeanSquare l <= 1 :=
    (div_le_one hM).mpr hle
  linarith

theorem s1939_hullScaleBound_of_scales
    (hscale : ∀ j : SignedLabel l.value, 1 <= (s1939RootPacket T).scale j) :
    s1939HullScaleBound T := by
  let i0 : Fin (lStar l.value) := ⟨lStar l.value - 1, by
    have hpos := s1930_lStar_pos l
    omega⟩
  let j0 : SignedLabel l.value := s1930PositiveLabel l i0
  have hj0val : (j0.1 : Real) = (lStar l.value : Real) := by
    have hnat : lStar l.value - 1 + 1 = lStar l.value := by
      have hpos := s1930_lStar_pos l
      omega
    have hR : (((lStar l.value - 1) + 1 : Nat) : Real) = (lStar l.value : Real) := by
      exact_mod_cast hnat
    push_cast at hR
    simp only [j0, s1930PositiveLabel_val, i0]
    push_cast
    exact hR
  have hj0sq : (j0.1 : Real) ^ 2 = (lStar l.value : Real) ^ 2 := by
    rw [hj0val]
  have hv : 0 <= s1939RootLogScale T j0 := by
    have h1 := hscale j0
    rw [s1939RootPacket_scale, Real.one_le_exp_iff] at h1
    exact h1
  have hS := s1939BadLog_neg T
  have hM := s1939MeanSquare_pos l
  have hSabs : s1939BadLog T = -|s1939BadLog T| := by
    linarith [abs_of_neg hS]
  rw [s1939RootLogScale, s1939LabelLog_eq, hj0sq, hSabs] at hv
  have hEq : 1 + (lStar l.value : Real) ^ 2 * (-|s1939BadLog T|) /
      s1939MeanSquare l =
      1 - ((lStar l.value : Real) ^ 2 * |s1939BadLog T|) /
        s1939MeanSquare l := by
    ring
  rw [hEq] at hv
  have hle : ((lStar l.value : Real) ^ 2 * |s1939BadLog T|) /
      s1939MeanSquare l <= 1 := by linarith
  exact (div_le_one hM).mp hle

theorem s1939_hullScaleBound_iff :
    (∀ j : SignedLabel l.value, 1 <= (s1939RootPacket T).scale j) ↔
      s1939HullScaleBound T :=
  ⟨s1939_hullScaleBound_of_scales T, s1939_hull_scales_ge_one T⟩

/-! ## 6. The actual root-packet determinant -/

/-- **The actual root-packet determinant of Corollary 3.12.**  Hull packet:
the exponential of the actual local log-magnitudes of the paper Theta values,
with the archimedean e-normalization and the paper j-normalization; unit
reference packet; determinant tensor power one; paper l* procession.  Its only
input is the hull-scale bound. -/
noncomputable def s1939Determinant (h : s1939HullScaleBound T) :
    SignedHullLogActual (SignedLabel l.value) where
  hullPacket := s1939RootPacket T
  referencePacket :=
    { scale := fun _ => 1
      positive := fun _ => Real.zero_lt_one }
  tensorPower := 1
  tensorPower_pos := Nat.one_pos
  hull_scales_ge_one := s1939_hull_scales_ge_one T h
  reference_scales_eq_one := fun _ => rfl
  procession := s1939Procession T
  procession_values := fun j => by
    show s1939RootLogScale T j =
      Real.log (Real.exp (s1939RootLogScale T j))
    rw [Real.log_exp]
  weights_nonnegative := fun j => by
    change 0 <= s1939Weight j
    unfold s1939Weight
    by_cases hj : 0 < j.1
    · rw [if_pos hj]
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · rw [if_neg hj]
  weightTotal_eq_one := rfl

@[simp] theorem s1939Determinant_hullPacket (h : s1939HullScaleBound T) :
    (s1939Determinant T h).hullPacket = s1939RootPacket T := rfl

@[simp] theorem s1939Determinant_procession (h : s1939HullScaleBound T) :
    (s1939Determinant T h).procession = s1939Procession T := rfl

theorem s1939_packetLogVolume_eq (h : s1939HullScaleBound T) :
    packetLogVolume (s1939RootPacket T) =
      (l.value : Real) + ((l.value : Real) - 1) * s1939BadLog T := by
  have hones : (∑ j : SignedLabel l.value, (1 : Real)) = (l.value : Real) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      SignedLabel.card_signedLabel]
    simp
  have hsq : (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) =
      (l.value : Real) * ((l.value : Real) ^ 2 - 1) / 12 := by
    have htoNat : ∀ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : Real) = (j.1 : Real) ^ 2 := by
      intro j
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (gaussExponent_nonneg j.1),
        s1939_gaussExponent_cast]
    rw [← s1930_gaussSum_eq l]
    exact Finset.sum_congr rfl (fun j _ => (htoNat j).symm)
  have hsqMean : (∑ j : SignedLabel l.value, (j.1 : Real) ^ 2) =
      ((l.value : Real) - 1) * s1939MeanSquare l := by
    rw [hsq]
    unfold s1939MeanSquare
    ring
  unfold packetLogVolume
  calc
    (∑ j : SignedLabel l.value, Real.log ((s1939RootPacket T).scale j))
        = ∑ j : SignedLabel l.value, s1939RootLogScale T j := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [s1939RootPacket_scale, Real.log_exp]
    _ = ∑ j : SignedLabel l.value,
          (1 + (j.1 : Real) ^ 2 * s1939BadLog T / s1939MeanSquare l) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [s1939RootLogScale, s1939LabelLog_eq]
    _ = (l.value : Real) + ((l.value : Real) - 1) * s1939BadLog T := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div]
          have hsum_mul : (∑ j : SignedLabel l.value,
              (j.1 : Real) ^ 2 * s1939BadLog T) =
              (((l.value : Real) - 1) * s1939MeanSquare l) * s1939BadLog T := by
            rw [← Finset.sum_mul, hsqMean]
          rw [hones, hsum_mul]
          field_simp [s1939MeanSquare_ne_zero l]

theorem s1939Determinant_hullLogVolume (h : s1939HullScaleBound T) :
    (s1939Determinant T h).hullLogVolume =
      (l.value : Real) + ((l.value : Real) - 1) * s1939BadLog T := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  simp only [s1939Determinant, Nat.cast_one, one_mul]
  exact s1939_packetLogVolume_eq T h

theorem s1939_bridge (h : s1939HullScaleBound T) :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1939Determinant T h) :=
  (s1915_bridge_iff_average_eq_a0 T (s1939Determinant T h)).mpr
    (s1939_average_eq_a0 T h)

/-- The paper signed-hull datum of Corollary 3.12 at the actual S1902 theta hull
and the actual root-packet determinant. -/
noncomputable def s1939Datum (h : s1939HullScaleBound T) :
    OrigXiFPaperSignedHullData (S1902Carrier T) l where
  thetaHull := s1902ActualThetaHull T
  determinant := s1939Determinant T h
  hull_logVolume_eq_procession := s1939_bridge T h

theorem s1939Datum_average (h : s1939HullScaleBound T) :
    (s1939Datum T h).determinant.procession.average = s1915A0 T :=
  s1939_average_eq_a0 T h

/-- **Corollary 3.12 at the actual root-packet determinant**: the paper
inequality -|log q| <= -|log Theta|. -/
theorem s1939_cor312 (h : s1939HullScaleBound T) :
    -|Real.log ‖S1487Cand.q‖| <=
      OrigXiFSignedThetaHullLogVolume (s1939Datum T h) :=
  s1880_xiF_inequality_abs (s1939Datum T h)

/-- The paper ray membership at the actual root-packet determinant. -/
theorem s1939_ray (h : s1939HullScaleBound T) :
    -|Real.log ‖S1487Cand.q‖| ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull (s1939Datum T h)).signedHullLogVolume :=
  s1880_xiF_paperSignedHullRay (s1939Datum T h)

/-! ## 7. The precise first missing -/

/-- **The precise first missing**: the hull-scale bound.  It is exactly the
statement that every actual root-packet scale is at least one; when it holds,
the construction above produces the determinant and the Corollary 3.12
inequality unconditionally.  It is a concrete real inequality on the actual
local qVFamily log-norms, not a log 5 identity and not a transcendence
statement. -/
def S1939FirstMissing : Prop := s1939HullScaleBound T

theorem s1939FirstMissing_iff_scales :
    S1939FirstMissing T ↔
      ∀ j : SignedLabel l.value, 1 <= (s1939RootPacket T).scale j :=
  (s1939_hullScaleBound_iff T).symm

theorem s1939FirstMissing_iff_abs_bound :
    S1939FirstMissing T ↔
      (lStar l.value : Real) ^ 2 * |s1939BadLog T| <= s1939MeanSquare l :=
  Iff.rfl

/-- The first missing written directly in the actual qVFamily unit norms. -/
theorem s1939FirstMissing_iff_qNorms :
    S1939FirstMissing T ↔
      (lStar l.value : Real) ^ 2 *
          |(1 / (2 * (l.value : Real))) *
            ∑ b : Bad (nativePlaceSelection T),
              (s1915LocalDegree T b : Real) *
                Real.log ‖(sourceRootQUnit T b : rootBase T b)‖|
        <= s1939MeanSquare l := by
  rw [S1939FirstMissing, s1939HullScaleBound, s1939BadLog_eq]

theorem s1939FirstMissing_bridge (h : S1939FirstMissing T) :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1939Determinant T h) :=
  s1939_bridge T h

/-! ## 8. The actual root-packet formula and the label-zero normalization -/

/-- The packet log-scale in the explicit actual-root-packet form: the
archimedean e-normalization plus the actual local log-magnitudes divided by the
paper j-normalization. -/
theorem s1939RootLogScale_eq (j : SignedLabel l.value) :
    s1939RootLogScale T j =
      1 + (1 / s1939MeanSquare l) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) *
            Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ := by
  unfold s1939RootLogScale s1939LabelLog s1939RootLog
  ring

/-- At the label j = 0 the actual theta value is one, so the packet log-scale
is exactly the archimedean normalization constant 1. -/
theorem s1939RootLogScale_zero :
    s1939RootLogScale T (s1930ZeroLabel l) = 1 := by
  rw [s1939RootLogScale_eq]
  have hzero : ∀ b : Bad (nativePlaceSelection T),
      Real.log ‖(rootNormedThetaValueInL T b (s1930ZeroLabel l) :
        rootNormedExtension T b)‖ = 0 := by
    intro b
    change s1939RootLog T b (s1930ZeroLabel l) = 0
    rw [s1939RootLog_eq, s1930ZeroLabel_val]
    norm_num
  rw [Finset.sum_eq_zero (fun b _ => by rw [hzero b]; ring)]
  ring

theorem s1939RootPacket_scale_zero :
    (s1939RootPacket T).scale (s1930ZeroLabel l) = Real.exp 1 := by
  rw [s1939RootPacket_scale, s1939RootLogScale_zero]

/-! ## 9. The paper signed-hull datum and Corollary 3.12 -/

theorem s1939Datum_signedLogVolume (h : s1939HullScaleBound T) :
    OrigXiFSignedThetaHullLogVolume (s1939Datum T h) = -s1915A0 T := by
  rw [OrigXiF.OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  rw [s1939Datum_average T h]

theorem s1939_nonempty_datum_of_bound (h : s1939HullScaleBound T) :
    Nonempty (OrigXiFPaperSignedHullData (S1902Carrier T) l) :=
  ⟨s1939Datum T h⟩

/-- The determinant hull log-volume in terms of a0 under the scale bound:
it is l * a0 - S = l * a0 + |S|. -/
theorem s1939Determinant_hullLogVolume_eq_a0 (h : s1939HullScaleBound T) :
    (s1939Determinant T h).hullLogVolume =
      (l.value : Real) * s1915A0 T + |s1939BadLog T| := by
  rw [s1939Determinant_hullLogVolume]
  have hS := s1939BadLog_neg T
  have ha0 : s1915A0 T = 1 + s1939BadLog T := by
    rw [s1915_a0_eq_closedForm T (le_of_lt (s1939_closedForm_pos T h))]
    exact s1939_closedForm_eq_badLog T
  have habs : |s1939BadLog T| = -s1939BadLog T := abs_of_neg hS
  rw [ha0, habs]
  ring

/-! ## 10. The precise first missing as an iff -/

theorem s1939_exists_bridge_iff_hullScaleBound :
    (∃ P : SignedHullLogActual (SignedLabel l.value),
        P.hullPacket = s1939RootPacket T ∧
          P.procession = s1939Procession T ∧
            S1904ProcessionBridge (s1902ActualThetaHull T) P) ↔
      s1939HullScaleBound T := by
  constructor
  · rintro ⟨P, hpacket, hproc, hbridge⟩
    refine s1939_hullScaleBound_of_scales T ?_
    intro j
    have h1 : 1 <= P.hullPacket.scale j := P.hull_scales_ge_one j
    rwa [hpacket] at h1
  · intro h
    exact ⟨s1939Determinant T h, rfl, rfl, s1939_bridge T h⟩

theorem s1939FirstMissing_iff_exists_bridge :
    S1939FirstMissing T ↔
      ∃ P : SignedHullLogActual (SignedLabel l.value),
        P.hullPacket = s1939RootPacket T ∧
          P.procession = s1939Procession T ∧
            S1904ProcessionBridge (s1902ActualThetaHull T) P :=
  (s1939_exists_bridge_iff_hullScaleBound T).symm

/-! ## 11. Axiom probes -/

#print axioms s1939LabelLog_eq
#print axioms s1939_average_eq_closedForm
#print axioms s1939_absBadLog_lt_one
#print axioms s1939_closedForm_pos
#print axioms s1939_average_eq_a0
#print axioms s1939_average_eq_a0_iff
#print axioms s1939_average_eq_a0_of_abs_le_one
#print axioms s1939_hull_scales_ge_one
#print axioms s1939_hullScaleBound_of_scales
#print axioms s1939_hullScaleBound_iff
#print axioms s1939Determinant
#print axioms s1939Determinant_hullLogVolume
#print axioms s1939Determinant_hullLogVolume_eq_a0
#print axioms s1939_bridge
#print axioms s1939Datum
#print axioms s1939Datum_average
#print axioms s1939Datum_signedLogVolume
#print axioms s1939_cor312
#print axioms s1939_ray
#print axioms s1939_exists_bridge_iff_hullScaleBound
#print axioms s1939FirstMissing_iff_exists_bridge
#print axioms s1939FirstMissing_iff_qNorms
#print axioms s1939RootLogScale_eq
#print axioms s1939RootLogScale_zero
#print axioms s1939RootPacket_scale_zero
#print axioms s1939Determinant_hullPacket
#print axioms s1939Determinant_procession
#print axioms s1939_nonempty_datum_of_bound
