import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.S1904ProcessionBridgeActual
import tmp.sheaf.xif.paper.S865RootHaarFactorNormPowActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual

/-!
# S1915: the actual value a0 of the S1902 Theta hull and its closed form

Layer: **O** (original-text Theta-link / xi-f, procession normalization).

Consumers:

* S1904 (tmp/sheaf/xif/paper/S1904ProcessionBridgeActual.lean): the
  procession bridge on the actual S1902 theta hull reads
  determinant.procession.average = a0 with
  a0 = (s1902LogVolume T (s1902Hull T)).toReal
  (s1915_bridge_iff_average_eq_a0);
* the S1880 D third field: the two-sided constraint 0 <= average <= 1
  transported to a0 (s1915_a0_nonneg, s1915_a0_le_one).

## Result of this file

0. The S1904 readout s1904HullLogVolume (s1902ActualThetaHull T) is
  definitionally the S1902 normalized hull log-volume; a0 is its real
  (toReal) value, and the S1904 bridge is exactly
  average = a0 (s1915_bridge_iff_average_eq_a0).

1. [PROVED] The two-sided bound 0 <= a0 <= 1.  The upper bound is the
  monotone normalization of the S1902 unit region; the lower bound is the
  ENNReal.toReal convention (ENNReal.toReal_nonneg).

2. [PROVED] The exact closed form.  Write
  d b = [K_b : Q_p] = Module.finrank Q_p (rootNormedExtension T b) and
  r b = rootImageRadius T b.  Then

      s1902LogVolume T (s1902Hull T)
        = ENNReal.ofReal (1 + sum_b d b * log (r b)),
      a0 = max 0 (1 + sum_b d b * log (r b)).

  Equivalently, the candidate closed form
  a0 = 1 + sum_b [K_b : Q_p] * log (rootImageRadius T b) holds exactly when
  its right-hand side is nonnegative (s1915_a0_eq_closedForm,
  s1915_a0_eq_closedForm_iff).  Since r b <= 1, the sum is <= 0, hence
  1 + sum_b ... <= 1, which gives the upper bound again.

  The proof is the project's actual factorization, with no fake equality:

  * Measure.pi_pi factorizes the actual product Haar over Bad;
  * rootExtensionProductHaar_unitBall identifies the product unit-ball mass;
  * the local Haar factor is the project's proven general norm-power formula
    rootHaarFactor_normPow_actual (S865),
    rootHaarFactor T b lam = ofReal (||lam|| ^ d b), applied to the actual
    maximizing field element rootThetaFieldLambda T b;
  * rootThetaFieldLambdaO_eq_closedBall and
    rootImageRadius_eq_norm_fieldLambda identify the local closed ball of
    radius rootImageRadius b with the field dilate of the unit ball;
  * rootExtensionProductImageHull_measure_pos_lt_top supplies positivity and
    finiteness of the actual hull mass, and the S1902 normalization
    exp 1 / mu(O).toReal supplies the additive constant 1.

## The exact boundary of the candidate identity

The only difference between the exact theorem and the literal candidate
a0 = 1 + sum_b ... is the ENNReal clipping built into the project's
haarLogVolume/toReal readout: when the unclipped real value is negative,
s1902LogVolume is 0 and a0 = 0, not the negative number.  This file
therefore proves the exact real identity with max 0, proves the candidate
under its exact hypothesis 0 <= 1 + sum_b ..., and proves that this hypothesis
is equivalent to the candidate (s1915_a0_eq_closedForm_iff).  Nothing is
asserted unconditionally and no equality is faked.  The local
norm/Haar-factor identification which older drafts recorded as a missing object
(RootHaarFactorNormPow) is not missing: S865 proves it.

No sorry, axiom, True/PUnit slot, or arbitrary datum is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual

open LeanFormal.IUT
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
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open LeanFormal.IUT.XiFPaper.S865RootHaarFactorNormPowActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaperThetaHull
open MeasureTheory
open scoped BigOperators Pointwise

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The value a0 and the candidate closed form -/

/-- The local degree [K_b : Q_p] of the root extension field. -/
noncomputable def s1915LocalDegree (b : Bad (nativePlaceSelection T)) : Nat :=
  Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)

/-- The actual real-valued normalized hull log-volume of the S1902 construction,
i.e. the a0 of S1904. -/
noncomputable def s1915A0 : Real :=
  (s1902LogVolume T (s1902Hull T)).toReal

/-- The actual product unit-ball mass (the denominator of the S1902
normalization). -/
noncomputable def s1915UnitMass : ENNReal :=
  rootExtensionProductHaar T (rootExtensionProductUnitBall T)

/-- The actual product hull mass. -/
noncomputable def s1915HullMass : ENNReal :=
  rootExtensionProductHaar T (rootExtensionProductImageHull T)

/-- The unclipped candidate closed form
1 + sum_b [K_b : Q_p] * log (rootImageRadius T b). -/
noncomputable def s1915ClosedForm : Real :=
  1 + ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)

/-! ## 2. Basic bounds on the local radii -/

/-- Every local radius is positive. -/
theorem s1915_rootImageRadius_pos (b : Bad (nativePlaceSelection T)) :
    0 < (rootImageRadius T b : Real) := by
  exact_mod_cast rootImageRadius_pos (T := T) (b := b)

/-- Every local radius is at most one: the actual theta image is integral in
the product unit ball (S664). -/
theorem s1915_rootImageRadius_le_one (b : Bad (nativePlaceSelection T)) :
    (rootImageRadius T b : Real) ≤ 1 := by
  have hbound : rootImageRadius T b ≤ 1 := by
    unfold rootImageRadius
    have hle : ∀ j : ThetaLabel (l := l),
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal) ≤ 1 := by
      intro j
      exact_mod_cast rootNormedThetaValueInL_norm_le_one (T := T) (b := b)
        (rootQUnitNormLeOne (T := T)) (thetaLabelToSigned (l := l) j)
    exact Finset.sup_le (fun j _ => hle j)
  exact_mod_cast hbound

/-- The maximizing field element is nonzero, because its norm is the (positive)
image radius. -/
theorem s1915_fieldLambda_ne_zero (b : Bad (nativePlaceSelection T)) :
    rootThetaFieldLambda T b ≠ 0 := by
  rw [← norm_pos_iff, ← rootImageRadius_eq_norm_fieldLambda]
  exact s1915_rootImageRadius_pos T b

/-- The unit of the local field attached to the maximizing field element. -/
noncomputable def s1915FieldLambdaUnit (b : Bad (nativePlaceSelection T)) :
    (rootNormedExtension T b)ˣ :=
  Units.mk0 (rootThetaFieldLambda T b) (s1915_fieldLambda_ne_zero T b)

/-! ## 3. The local Haar factor: field dilate of the unit ball -/

/-- The actual local Haar factor of the maximizing field element is its norm to
the local degree.  This is the project's general norm-power formula (S865). -/
theorem s1915_localFactor_eq (b : Bad (nativePlaceSelection T)) :
    rootHaarFactor T b (s1915FieldLambdaUnit T b) =
      ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b) := by
  have h := rootHaarFactor_normPow_actual (l := l) (T := T) (b := b)
    (s1915FieldLambdaUnit T b)
  have hnorm : ‖((s1915FieldLambdaUnit T b : rootNormedExtension T b))‖ =
      (rootImageRadius T b : Real) := by
    change ‖rootThetaFieldLambda T b‖ = (rootImageRadius T b : Real)
    exact (rootImageRadius_eq_norm_fieldLambda (T := T) (b := b)).symm
  rw [h, hnorm]
  unfold s1915LocalDegree
  rfl

/-- The actual local closed ball of radius rootImageRadius b is the field
dilate of the local unit ball. -/
theorem s1915_localClosedBall_eq (b : Bad (nativePlaceSelection T)) :
    Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real) =
      s1915FieldLambdaUnit T b • rootExtensionUnitBall T b := by
  rw [rootImageRadius_eq_norm_fieldLambda]
  rw [← rootThetaFieldLambdaO_eq_closedBall]
  rfl

/-- The actual local measure of the closed ball of radius rootImageRadius b
is the norm-power factor times the unit-ball mass. -/
theorem s1915_local_measure (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : Real)) =
      ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  have hpos : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0 :=
    ne_of_gt (rootExtensionUnitBall_measure_pos (T := T) (b := b))
  have hfin : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤ :=
    ne_of_lt (rootExtensionUnitBall_measure_lt_top (T := T) (b := b))
  have hratio : ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b) =
      rootExtensionHaar T b (s1915FieldLambdaUnit T b • rootExtensionUnitBall T b) /
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
    rw [← s1915_localFactor_eq]
    exact rootHaarFactor_eq_ratio (T := T) (b := b) (s1915FieldLambdaUnit T b)
  rw [s1915_localClosedBall_eq, hratio, ENNReal.div_mul_cancel hpos hfin]

/-! ## 4. Product factorization of the actual Haar measure -/

/-- Positivity of the product unit-ball mass. -/
theorem s1915_unitMass_pos : 0 < s1915UnitMass T :=
  (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).1

/-- Finiteness of the product unit-ball mass. -/
theorem s1915_unitMass_lt_top : s1915UnitMass T < ⊤ :=
  (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).2

/-- Positivity of the product hull mass. -/
theorem s1915_hullMass_pos : 0 < s1915HullMass T :=
  (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).1

/-- Finiteness of the product hull mass. -/
theorem s1915_hullMass_lt_top : s1915HullMass T < ⊤ :=
  (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2

/-- Product Haar factorization: the actual product hull mass is the product of
the actual local norm-power factors times the product unit-ball mass. -/
theorem s1915_hull_measure_eq :
    s1915HullMass T =
      (∏ b : Bad (nativePlaceSelection T),
        ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b)) *
        s1915UnitMass T := by
  unfold s1915HullMass s1915UnitMass rootExtensionProductImageHull
    rootExtensionProductUnitBall
  unfold rootExtensionProductHaar
  simp only [Measure.pi_pi]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun b _ => s1915_local_measure T b)

/-- The same factorization at the level of the real (toReal) hull mass. -/
theorem s1915_hull_toReal :
    (s1915HullMass T).toReal =
      (∏ b : Bad (nativePlaceSelection T),
        (rootImageRadius T b : Real) ^ s1915LocalDegree T b) *
        (s1915UnitMass T).toReal := by
  calc
    (s1915HullMass T).toReal
        = ((∏ b : Bad (nativePlaceSelection T),
            ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b)) *
            s1915UnitMass T).toReal := by rw [s1915_hull_measure_eq]
    _ = (∏ b : Bad (nativePlaceSelection T),
            ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b)).toReal *
          (s1915UnitMass T).toReal := ENNReal.toReal_mul
    _ = (∏ b : Bad (nativePlaceSelection T),
            (rootImageRadius T b : Real) ^ s1915LocalDegree T b) *
          (s1915UnitMass T).toReal := by
          simp only [ENNReal.toReal_prod]
          congr 1
          exact Finset.prod_congr rfl
            (fun b _ => ENNReal.toReal_ofReal (by positivity))

/-- The logarithm of the product of the local norm powers. -/
theorem s1915_log_prod_radius :
    Real.log (∏ b : Bad (nativePlaceSelection T),
        (rootImageRadius T b : Real) ^ s1915LocalDegree T b) =
      ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) := by
  rw [Real.log_prod (f := fun b : Bad (nativePlaceSelection T) =>
      (rootImageRadius T b : Real) ^ s1915LocalDegree T b)
    (fun b _ => pow_ne_zero _ (ne_of_gt (s1915_rootImageRadius_pos T b)))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Real.log_pow]

/-! ## 5. The normalized hull mass and its logarithm -/

/-- The actual normalized hull mass is the S1902 rescaling of the actual hull
mass. -/
theorem s1915_normalized_hull_toReal :
    (s1902NormalizedHaar T (s1902Hull T)).toReal =
      (Real.exp 1 / (s1915UnitMass T).toReal) * (s1915HullMass T).toReal := by
  unfold s1902NormalizedHaar s1902HaarScale s1902Hull s1915HullMass s1915UnitMass
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  congr 1
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- The logarithm of the actual normalized hull mass is the unclipped closed
form. -/
theorem s1915_log_normalized_hull :
    Real.log (s1902NormalizedHaar T (s1902Hull T)).toReal = s1915ClosedForm T := by
  have hUpos : 0 < (s1915UnitMass T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (s1915_unitMass_pos T))
      (ne_of_lt (s1915_unitMass_lt_top T))
  have hHpos : 0 < (s1915HullMass T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (s1915_hullMass_pos T))
      (ne_of_lt (s1915_hullMass_lt_top T))
  have hprodpos : 0 < ∏ b : Bad (nativePlaceSelection T),
      (rootImageRadius T b : Real) ^ s1915LocalDegree T b :=
    Finset.prod_pos (fun b _ => pow_pos (s1915_rootImageRadius_pos T b) _)
  rw [s1915_normalized_hull_toReal]
  rw [Real.log_mul (div_ne_zero (Real.exp_pos 1).ne' (ne_of_gt hUpos))
    (ne_of_gt hHpos)]
  rw [Real.log_div (Real.exp_pos 1).ne' (ne_of_gt hUpos)]
  rw [s1915_hull_toReal, Real.log_mul (ne_of_gt hprodpos) (ne_of_gt hUpos)]
  rw [s1915_log_prod_radius, Real.log_exp]
  unfold s1915ClosedForm
  ring

/-- Exact value of the S1902 normalized hull log-volume: it is the
ENNReal.ofReal of the unclipped closed form. -/
theorem s1915_logVolume_eq :
    s1902LogVolume T (s1902Hull T) = ENNReal.ofReal (s1915ClosedForm T) := by
  unfold s1902LogVolume
  have hfin : s1902NormalizedHaar T (s1902Hull T) < ⊤ := by
    have hle : s1902NormalizedHaar T (s1902Hull T) ≤
        s1902NormalizedHaar T (s1902UnitRegion T) :=
      measure_mono (s1902Hull_subset_unitRegion T)
    rw [s1902NormalizedHaar_unitRegion] at hle
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  rw [haarLogVolume_of_lt_top hfin]
  rw [s1915_log_normalized_hull]

/-! ## 6. The value a0: bounds and the closed form -/

/-- The exact value of a0: the unclipped closed form clipped at zero. -/
theorem s1915_a0_eq_max :
    s1915A0 T = max 0 (s1915ClosedForm T) := by
  unfold s1915A0
  rw [s1915_logVolume_eq]
  by_cases h : 0 ≤ s1915ClosedForm T
  · rw [ENNReal.toReal_ofReal h, max_eq_right h]
  · have h' : s1915ClosedForm T ≤ 0 := le_of_lt (not_le.mp h)
    rw [ENNReal.ofReal_eq_zero.mpr h', ENNReal.toReal_zero, max_eq_left h']

/-- The candidate closed form, with its exact hypothesis.  If the unclipped
closed form is nonnegative, then a0 equals
1 + sum_b [K_b : Q_p] * log (rootImageRadius T b). -/
theorem s1915_a0_eq_closedForm (h : 0 ≤ s1915ClosedForm T) :
    s1915A0 T = s1915ClosedForm T := by
  rw [s1915_a0_eq_max, max_eq_right h]

/-- The candidate closed-form identity is equivalent to the nonnegativity of its
right-hand side: the only obstruction is the ENNReal clipping of the project's
haarLogVolume. -/
theorem s1915_a0_eq_closedForm_iff :
    s1915A0 T = s1915ClosedForm T ↔ 0 ≤ s1915ClosedForm T := by
  rw [s1915_a0_eq_max]
  constructor
  · intro h
    rw [← h]
    exact le_max_left 0 (s1915ClosedForm T)
  · intro h
    exact max_eq_right h

/-- When the unclipped closed form is nonpositive, a0 is zero. -/
theorem s1915_a0_eq_zero_of_closedForm_nonpos (h : s1915ClosedForm T ≤ 0) :
    s1915A0 T = 0 := by
  rw [s1915_a0_eq_max, max_eq_left h]

/-- The unclipped closed form is at most one: every local radius is at most
one. -/
theorem s1915_closedForm_le_one : s1915ClosedForm T ≤ 1 := by
  unfold s1915ClosedForm
  have hsum : (∑ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)) ≤ 0 := by
    refine Finset.sum_nonpos (fun b _ => ?_)
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
      (Real.log_nonpos (s1915_rootImageRadius_pos T b).le
        (s1915_rootImageRadius_le_one T b))
  linarith

/-- The lower bound 0 <= a0. -/
theorem s1915_a0_nonneg : 0 ≤ s1915A0 T := by
  unfold s1915A0
  exact ENNReal.toReal_nonneg

/-- The upper bound a0 <= 1. -/
theorem s1915_a0_le_one : s1915A0 T ≤ 1 := by
  rw [s1915_a0_eq_max]
  exact max_le (by norm_num) (s1915_closedForm_le_one T)

/-- The two-sided bound on the actual value. -/
theorem s1915_a0_mem_Icc : 0 ≤ s1915A0 T ∧ s1915A0 T ≤ 1 :=
  ⟨s1915_a0_nonneg T, s1915_a0_le_one T⟩

/-! ## 7. The S1904 bridge as average = a0 -/

/-- The S1904 hull-log-volume readout on the S1902 theta hull is the S1902
normalized log-volume. -/
theorem s1915_hullLogVolume_eq :
    s1904HullLogVolume (s1902ActualThetaHull T) =
      s1902LogVolume T (s1902Hull T) := rfl

/-- The S1904 procession bridge is exactly average = a0 on the actual S1902
theta hull. -/
theorem s1915_bridge_iff_average_eq_a0
    (P : SignedHullLogActual (SignedLabel l.value)) :
    S1904ProcessionBridge (s1902ActualThetaHull T) P ↔
      s1904ProcessionAverage P = s1915A0 T := by
  rw [s1904_bridge_iff_toReal]
  rfl

/-- Any determinant satisfying the bridge has procession average a0. -/
theorem s1915_average_eq_a0_of_bridge
    (P : SignedHullLogActual (SignedLabel l.value))
    (h : S1904ProcessionBridge (s1902ActualThetaHull T) P) :
    s1904ProcessionAverage P = s1915A0 T :=
  (s1915_bridge_iff_average_eq_a0 T P).mp h

/-- Any determinant satisfying the bridge has procession average in [0,1],
and its average is a0. -/
theorem s1915_average_mem_Icc_of_bridge
    (P : SignedHullLogActual (SignedLabel l.value))
    (h : S1904ProcessionBridge (s1902ActualThetaHull T) P) :
    0 ≤ s1904ProcessionAverage P ∧ s1904ProcessionAverage P ≤ 1 := by
  rw [s1915_average_eq_a0_of_bridge T P h]
  exact s1915_a0_mem_Icc T

/-! ## 8. Axiom probes -/

#print axioms s1915_localFactor_eq
#print axioms s1915_local_measure
#print axioms s1915_hull_measure_eq
#print axioms s1915_log_normalized_hull
#print axioms s1915_logVolume_eq
#print axioms s1915_a0_eq_max
#print axioms s1915_a0_eq_closedForm
#print axioms s1915_a0_nonneg
#print axioms s1915_a0_le_one
#print axioms s1915_bridge_iff_average_eq_a0

end LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual

end
