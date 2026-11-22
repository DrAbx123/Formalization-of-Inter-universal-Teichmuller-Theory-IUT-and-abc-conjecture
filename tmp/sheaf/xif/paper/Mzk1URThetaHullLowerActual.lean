/- U-R C2 J1: exact volume of the value-group ceiling region (kurt).

THIS FILE ONLY uses maxHeartbeats 1000000 (Lead-approved adapter budget).

Contents (unconditional): the value-group ceiling urCeilC of the half root
coefficient, an actual generator of norm p^(-urCeilC), the value-group scaling
data, and the exact normalized log-volume
  mu_log(F(urCeilC) * O_hol) = -(urCeilC) * log p.
This is the volume input for the unconditional theta upper/lower bounds. -/
import tmp.sheaf.xif.paper.Mzk1URThetaHullNonzeroActual
import tmp.sheaf.xif.paper.Mzk1ULStepVHullPaperActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullLowerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepVHullPaperActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The factor field of the bad place. -/
abbrev urLowerK (b : Bad (nativePlaceSelection T)) : Type :=
  CommonPrimeCompletion ((qVFamTensorPlaces T b) () (qVFamTensorTuple ()))

/-- The ramification exponent of the factor field. -/
noncomputable def urLowerE (b : Bad (nativePlaceSelection T)) : ℕ :=
  logShellRamificationExponent (K := urLowerK T b) (p := qVFamTensorP T b)

/-- The half root coefficient is nonnegative. -/
theorem urRootCoeff_nonneg' (b : Bad (nativePlaceSelection T)) :
    0 ≤ actualRootCoeff (l := l) T b () :=
  urRootCoeff_nonneg (l := l) T b

/-- The half root coefficient is positive. -/
theorem urRootCoeff_pos (b : Bad (nativePlaceSelection T)) :
    0 < actualRootCoeff (l := l) T b () := by
  unfold actualRootCoeff
  have hl : (0 : ℝ) < (2 * (l.value : ℝ)) := by
    have h5 : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
    linarith
  have hc : 0 < QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b :=
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient_pos (T := T) (b := b)
  exact div_pos hc hl

/-- The value-group ceiling exponent of the half root coefficient. -/
noncomputable def urGaussK (b : Bad (nativePlaceSelection T)) : ℤ :=
  Int.ceil (actualRootCoeff (l := l) T b () * (urLowerE (l := l) T b : ℝ))

/-- The ceiling exponent is positive. -/
theorem urGaussK_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ urGaussK (l := l) T b := by
  unfold urGaussK
  apply Int.ceil_nonneg
  have hc := urRootCoeff_nonneg' (l := l) T b
  have he : (0 : ℝ) ≤ (urLowerE (l := l) T b : ℝ) := by positivity
  exact mul_nonneg hc he

/-- The value-group ceiling of the half root coefficient. -/
noncomputable def urCeilC (b : Bad (nativePlaceSelection T)) : ℝ :=
  (urGaussK (l := l) T b : ℝ) / (urLowerE (l := l) T b : ℝ)

/-- The ceiling equals the generic ceilExp of the half root coefficient. -/
theorem urCeilC_eq (b : Bad (nativePlaceSelection T)) :
    urCeilC (l := l) T b =
      urCeilCoeff (l := l) T b (actualRootCoeff (l := l) T b ()) := by
  unfold urCeilC urCeilCoeff ceilExp urGaussK urLowerE urLowerK
  rfl

/-- The actual value-group generator at the ceiling. -/
noncomputable def urCeilGenerator (b : Bad (nativePlaceSelection T)) :
    urLowerK T b :=
  ((↑(arithmeticTupleLocalUniformizer (qVFamTensorPlaces T b) qVFamTensorTuple () :
      urLowerK T b)) ^ (urGaussK (l := l) T b).toNat)

/-- Nonnegative ceiling exponent as a real number. -/
theorem urGaussK_toNat_cast (b : Bad (nativePlaceSelection T)) :
    ((urGaussK (l := l) T b).toNat : ℝ) = (urGaussK (l := l) T b : ℝ) := by
  have h : 0 ≤ urGaussK (l := l) T b := urGaussK_nonneg (l := l) T b
  rw [show ((urGaussK (l := l) T b).toNat : ℝ) =
      (((urGaussK (l := l) T b).toNat : ℤ) : ℝ) from by push_cast; ring]
  rw [Int.toNat_of_nonneg h]

/-- The generator has norm p^(-ceil). -/
theorem urCeilGenerator_norm (b : Bad (nativePlaceSelection T)) :
    ‖urCeilGenerator (l := l) T b‖ =
      (qVFamTensorP T b : ℝ) ^ (-(urCeilC (l := l) T b)) := by
  unfold urCeilGenerator urCeilC
  rw [norm_pow, norm_uniformizer_eq_prime_rpow_inv_ramificationExponent
    (p := qVFamTensorP T b) (K := urLowerK T b)
    (arithmeticTupleLocalUniformizer (qVFamTensorPlaces T b) qVFamTensorTuple ())
    (arithmeticTupleLocalUniformizer_irreducible (qVFamTensorPlaces T b) qVFamTensorTuple
      ())]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  rw [urGaussK_toNat_cast (l := l) T b]
  rw [show -(1 / (logShellRamificationExponent
        (K := urLowerK T b) (p := qVFamTensorP T b) : ℝ)) *
        (urGaussK (l := l) T b : ℝ) =
      -((urGaussK (l := l) T b : ℝ) / (logShellRamificationExponent
        (K := urLowerK T b) (p := qVFamTensorP T b) : ℝ)) from by
    rw [div_eq_mul_inv]
    ring]
  rfl

/-- The value-group scaling data at the ceiling exponent. -/
noncomputable def urCeilData (b : Bad (nativePlaceSelection T)) :
    ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun _ => urCeilC (l := l) T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple) (p := qVFamTensorP T b)
    (c := fun _ => urCeilC (l := l) T b)
    (g := fun _ => urCeilGenerator (l := l) T b)
    (hg := fun _ => urCeilGenerator_norm (l := l) T b)

/-- Exact normalized log-volume of the ceiling region. -/
theorem urCeilRegion_logVolume (b : Bad (nativePlaceSelection T)) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar
        ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
            (fun _ => urCeilC (l := l) T b) *
          arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
            Submodule ℤ_[qVFamTensorP T b] (qVFamTensorBlock T b)) :
          Set (qVFamTensorBlock T b)) =
      -(urCeilC (l := l) T b * Real.log (qVFamTensorP T b : ℝ)) := by
  have h := arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (urCeilData (l := l) T b)
  rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, nsmul_eq_mul]
  norm_num


/-! ## The label-1 region has the same exact log-volume -/

/-- The label-1 theta coefficient vector is the constant half root coefficient. -/
theorem urOneLabelCoeff_eq (b : Bad (nativePlaceSelection T)) :
    (fun _ : qVFamTensorV =>
        ((gaussExponent (oneLabel l).1).toNat : ℝ) * actualRootCoeff (l := l) T b ()) =
      (fun _ => actualRootCoeff (l := l) T b ()) := by
  funext i
  rw [gaussExponent_oneLabel]
  norm_num

/-- The constant half coefficient lattice equals the ceiling lattice. -/
theorem urFracConst_eq (b : Bad (nativePlaceSelection T)) :
    arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ => actualRootCoeff (l := l) T b ()) =
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ => urCeilC (l := l) T b) := by
  apply Mzk1URThetaHullTensorActual.arithmeticTupleFractionalLattice_congr
  intro i
  rw [urCeilC_eq (l := l) T b]
  exact urLocal_ball_eq_ceil (l := l) T b (actualRootCoeff (l := l) T b ())
    (urRootCoeff_nonneg' (l := l) T b)

/-- The label-1 theta region is the ceiling region. -/
theorem urLabelOneRegion_eq_ceilRegion (b : Bad (nativePlaceSelection T)) :
    actualRootThetaRegion (l := l) T b (oneLabel l) =
      thetaTensorScaledRegion (qVFamTensorPlaces T b) qVFamTensorTuple
        (fun _ => urCeilC (l := l) T b) := by
  unfold actualRootThetaRegion thetaTensorScaledRegion
  rw [urOneLabelCoeff_eq (l := l) T b, urFracConst_eq (l := l) T b]

/-- Exact log-volume of the label-1 theta region. -/
theorem urLabelOneRegion_logVolume (b : Bad (nativePlaceSelection T)) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (actualRootThetaRegion (l := l) T b (oneLabel l)) =
      -(urCeilC (l := l) T b * Real.log (qVFamTensorP T b : ℝ)) := by
  rw [urLabelOneRegion_eq_ceilRegion (l := l) T b]
  unfold thetaTensorScaledRegion at ⊢
  exact urCeilRegion_logVolume (l := l) T b



/-! ## The actual per-bad-place paper Step(v) bound (no free parameters) -/

/-- The actual exceptional set of the bad-place packet (paper I*). -/
noncomputable def urPacketExceptional (b : Bad (nativePlaceSelection T)) :
    Finset qVFamTensorV :=
  Finset.univ.filter (fun i => qVFamTensorP T b - 2 <
    logShellRamificationExponent
      (K := CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
      (p := qVFamTensorP T b))

/-- The actual total different order of the packet. -/
noncomputable def urPacketDifferentSum (b : Bad (nativePlaceSelection T)) : ℝ :=
  ∑ i : qVFamTensorV, localNormOrder (qVFamTensorP T b)
    (arithmeticTupleLocalDifferent (qVFamTensorPlaces T b) qVFamTensorTuple i)

/-- The actual per-bad-place paper Step(v) bound: the packet value V_b
(no free parameters; lambda = urCeilC). -/
noncomputable def urPacketV (b : Bad (nativePlaceSelection T)) : ℝ :=
  (-(urCeilC (l := l) T b) + urPacketDifferentSum (l := l) T b + 1) *
      Real.log (qVFamTensorP T b : ℝ) +
    urStepVExcSum (qVFamTensorPlaces T b) qVFamTensorTuple
      (urPacketExceptional (l := l) T b)

#print axioms urPacketExceptional
#print axioms urPacketDifferentSum
#print axioms urPacketV

#print axioms urOneLabelCoeff_eq
#print axioms urFracConst_eq
#print axioms urLabelOneRegion_eq_ceilRegion
#print axioms urLabelOneRegion_logVolume
#print axioms urCeilC_eq
#print axioms urCeilGenerator_norm
#print axioms urCeilRegion_logVolume

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullLowerActual
end