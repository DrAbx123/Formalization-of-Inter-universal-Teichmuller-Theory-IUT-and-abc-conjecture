import tmp.sheaf.xif.paper.QVFamTensorCoefficientInclusionActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.SignedHullNormalizationActual

/-!
# Minimal per-b scalar carrier for the qVFamily Theta hull

Minimal-carrier audit result: the xi-f scalar is the weighted sum, over the
actual bad places b, of the local normalized log-volume on the one-factor
fractional tensor block at b.  No product hull carrier and no canonical tuple
block are required for this scalar.

This file keeps only:

* the actual per-b lambda-O fractional lattice region;
* the actual theta scaled-region containment in that region;
* the uniform identical-copy signed-label average equal to the local log;
* the actual qVFamily coefficient positivity and coefficient log nonzero.

The local Haar positivity/finiteness and the paper procession normalization
equality are recorded as exact actual gaps, not assumed.

No product hull, no canonical tuple block, no LGP/Kummer/Ind, no fake data.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QVFamScalarPrerequisitesActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientInclusionActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.SignedHullNormalizationActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The actual per-b q-pilot lambda-O region on the one-factor tensor block. -/
noncomputable abbrev qVFamLambdaOHull : Set (qVFamTensorBlock T b) :=
  qVFamQPilotRegion T b

/-- The actual theta scaled region at a signed label lands in the actual
per-b lambda-O region. -/
theorem qVFamThetaScaledRegion_subset_lambdaOHull
    (j : SignedLabel l.value)
    (hj : 1 ≤ (gaussExponent j.1).toNat) :
    qVFamThetaTensorRegion T b j ⊆ qVFamLambdaOHull T b :=
  qVFamThetaTensorRegion_subset_qPilotRegion T b j hj

/-- The finite signed-label uniform procession whose copies are all the actual
local normalized log-volume. -/
noncomputable def qVFamUniformProcession :
    WeightedValues (sourceFiniteLabel l) where
  value _ := qVFamLocalThetaHullLogVolume T b
  weight _ := (Fintype.card (sourceFiniteLabel l) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (sourceFiniteLabel l) : Real) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := sourceFiniteLabel l)
    exact (mul_inv_cancel₀ hcard).symm

/-- Every copy has the same local value. -/
theorem qVFamUniformProcession_value
    (j : sourceFiniteLabel l) :
    (qVFamUniformProcession T b).value j =
      qVFamLocalThetaHullLogVolume T b := rfl

/-- The finite average equals the local normalized log-volume, because the
copies are identical. -/
theorem qVFamUniformProcession_average :
    (qVFamUniformProcession T b).average =
      qVFamLocalThetaHullLogVolume T b := by
  unfold WeightedValues.average qVFamUniformProcession
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_one]
  have hcard : (Fintype.card (sourceFiniteLabel l) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := sourceFiniteLabel l)
  field_simp [hcard]

/-- The actual qVFamily coefficient is strictly positive. -/
theorem qVFamTensorCoefficient_pos :
    0 < qVFamTensorCoefficient T b := by
  unfold qVFamTensorCoefficient
  exact_mod_cast (qVFamily T b).order_pos

/-- The actual coefficient log is nonzero: c > 0 and p > 1. -/
theorem qVFamTensorCoefficient_log_ne_zero :
    -(qVFamTensorCoefficient T b) *
        Real.log (qVFamP T b : Real) ≠ 0 := by
  have hp : (1 : Real) < (qVFamP T b : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamP T b)).one_lt
  have hlogp : Real.log (qVFamP T b : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hp)
  have hc : qVFamTensorCoefficient T b ≠ 0 :=
    ne_of_gt (qVFamTensorCoefficient_pos T b)
  exact mul_ne_zero (neg_ne_zero.mpr hc) hlogp

/-- Exact actual local normalization gap: the per-b local unit/hull Haar
positivity/finiteness and the paper procession normalization equality are not
supplied by the coefficient data. -/
structure QVFamLocalNormalizationGap : Prop where
  localUnitHaarPos : Prop
  localUnitHaarFinite : Prop
  localHullHaarPos : Prop
  localHullHaarFinite : Prop
  localLogEqPaperProcessionAverage : Prop

/-- The exact missing local normalization object. -/
def QVFamLocalNormalizationGapRequired : Prop :=
  Nonempty (QVFamLocalNormalizationGap (l := l) (T := T) (b := b))

/-- Minimal xi-f scalar carrier data: only the per-b one-factor tensor block,
its actual lambda-O region, the scaled-region containment, the identical-copy
procession average, coefficient positivity/log nonzero, and the exact local
normalization gap. -/
structure QVFamScalarPrerequisiteData where
  lambdaOHull : Set (qVFamTensorBlock T b)
  lambdaOHull_eq : lambdaOHull = qVFamLambdaOHull T b
  imageScaled_subset_hull :
    ∀ (j : SignedLabel l.value),
      1 ≤ (gaussExponent j.1).toNat →
        qVFamThetaTensorRegion T b j ⊆ lambdaOHull
  procession : WeightedValues (sourceFiniteLabel l)
  procession_eq : procession = qVFamUniformProcession T b
  procession_average_eq_local :
    procession.average = qVFamLocalThetaHullLogVolume T b
  coefficient_pos : 0 < qVFamTensorCoefficient T b
  coefficient_log_ne_zero :
    -(qVFamTensorCoefficient T b) *
      Real.log (qVFamP T b : Real) ≠ 0
  localNormalizationGap : Prop
  localNormalizationGap_eq : localNormalizationGap =
    QVFamLocalNormalizationGapRequired (l := l) (T := T) (b := b)

/-- Actual minimal-carrier inhabitant. -/
noncomputable def qvFamScalarPrerequisiteData :
    QVFamScalarPrerequisiteData T b where
  lambdaOHull := qVFamLambdaOHull T b
  lambdaOHull_eq := rfl
  imageScaled_subset_hull := fun j hj =>
    qVFamThetaScaledRegion_subset_lambdaOHull T b j hj
  procession := qVFamUniformProcession T b
  procession_eq := rfl
  procession_average_eq_local := qVFamUniformProcession_average T b
  coefficient_pos := qVFamTensorCoefficient_pos T b
  coefficient_log_ne_zero := qVFamTensorCoefficient_log_ne_zero T b
  localNormalizationGap := QVFamLocalNormalizationGapRequired (l := l) (T := T) (b := b)
  localNormalizationGap_eq := rfl

end LeanFormal.IUT.XiFPaper.QVFamScalarPrerequisitesActualAdapted
end
