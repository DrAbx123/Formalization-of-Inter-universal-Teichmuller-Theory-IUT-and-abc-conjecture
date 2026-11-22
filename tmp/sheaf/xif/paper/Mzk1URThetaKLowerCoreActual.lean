/- U-R C2 J1 (P): K-side exact volume of the value-group ceiling region (kurt).

Same proof as the F-side lower file, re-instantiated on the K-completion carrier
(ksPlaces/ksTuple/ksP from Mzk1ULKSideLettersActual via Mzk1URThetaKSideActual).
Unconditional: value-group ceiling urCeilC of the half root coefficient, generator
of norm p^(-urCeilC), scaling data, and
  mu_log(F(urCeilC) * O_hol) = -(urCeilC) * log p
on the K-side tensor block.

THIS FILE ONLY uses maxHeartbeats 1000000 (Lead-approved adapter budget). -/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaPureGeneratorActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullNonzeroActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullTensorActual
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

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual

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
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The factor field of the bad place. -/
abbrev urLowerK (b : Bad (nativePlaceSelection T)) : Type :=
  CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))

/-- The Qp-normed-algebra instance at the bad K-place, keyed by the actual places
computation (raw rational prime, matching sophie's R1 syntax). -/
noncomputable instance ksLowerNormedAlgebra (b : Bad (nativePlaceSelection T)) :
    NormedAlgebra ℚ_[(completionRationalPrime (nativeBadToKPlace T b)).val]
      (CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))) :=
  commonPrimeCompletionNormedAlgebra ((ksPlaces T b) () (ksTuple ()))

/-- The ramification exponent of the factor field. -/
noncomputable def urLowerE (b : Bad (nativePlaceSelection T)) : ℕ :=
  logShellRamificationExponent (K := urLowerK T b) (p := (completionRationalPrime (nativeBadToKPlace T b)).val)

/-- The half root coefficient is nonnegative. -/
theorem urRootCoeff_nonneg' (b : Bad (nativePlaceSelection T)) :
    0 ≤ actualRootCoeff (l := l) T b () := by
  unfold actualRootCoeff
  exact div_nonneg (qVFamNormalizedCoefficient_nonneg T b) (by positivity)

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

/-- The value-group ceiling of a coefficient at the K-side factor. -/
noncomputable def ksCeilCoeff (b : Bad (nativePlaceSelection T)) (c : ℝ) : ℝ :=
  ceilExp (p := (completionRationalPrime (nativeBadToKPlace T b)).val) (K := CommonPrimeCompletion (ksPlace T b)) c

/-- The ceiling equals the generic ceilExp of the half root coefficient. -/
theorem urCeilC_eq (b : Bad (nativePlaceSelection T)) :
    urCeilC (l := l) T b =
      ksCeilCoeff (l := l) T b (actualRootCoeff (l := l) T b ()) := by
  unfold urCeilC ksCeilCoeff ceilExp urGaussK urLowerE urLowerK
  rfl

/-- The actual value-group generator at the ceiling. -/
noncomputable def urCeilGenerator (b : Bad (nativePlaceSelection T)) :
    urLowerK T b :=
  ((↑(arithmeticTupleLocalUniformizer (ksPlaces T b) ksTuple () :
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
      ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ) ^ (-(urCeilC (l := l) T b)) := by
  unfold urCeilGenerator urCeilC
  rw [norm_pow, norm_uniformizer_eq_prime_rpow_inv_ramificationExponent
    (p := (completionRationalPrime (nativeBadToKPlace T b)).val) (K := urLowerK T b)
    (arithmeticTupleLocalUniformizer (ksPlaces T b) ksTuple ())
    (arithmeticTupleLocalUniformizer_irreducible (ksPlaces T b) ksTuple
      ())]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  rw [urGaussK_toNat_cast (l := l) T b]
  rw [show -(1 / (logShellRamificationExponent
        (K := urLowerK T b) (p := (completionRationalPrime (nativeBadToKPlace T b)).val) : ℝ)) *
        (urGaussK (l := l) T b : ℝ) =
      -((urGaussK (l := l) T b : ℝ) / (logShellRamificationExponent
        (K := urLowerK T b) (p := (completionRationalPrime (nativeBadToKPlace T b)).val) : ℝ)) from by
    rw [div_eq_mul_inv]
    ring]
  rfl

/-- The value-group scaling data at the ceiling exponent. -/
noncomputable def urCeilData (b : Bad (nativePlaceSelection T)) :
    ArithmeticTuplePureFractionalScalingData (ksPlaces T b) ksTuple
      (fun _ => urCeilC (l := l) T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (places := ksPlaces T b) (tuple := ksTuple) (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    (c := fun _ => urCeilC (l := l) T b)
    (g := fun _ => urCeilGenerator (l := l) T b)
    (hg := fun _ => urCeilGenerator_norm (l := l) T b)

/-- Exact normalized log-volume of the ceiling region. -/
theorem urCeilRegion_logVolume (b : Bad (nativePlaceSelection T)) :
    arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        Measure.addHaar
        ((arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
            (fun _ => urCeilC (l := l) T b) *
          arithmeticTupleHolomorphicLattice (ksPlaces T b) ksTuple :
            Submodule ℤ_[(completionRationalPrime (nativeBadToKPlace T b)).val] (ksBlock T b)) :
          Set (ksBlock T b)) =
      -(urCeilC (l := l) T b * Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)) := by
  have h := arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (ksPlaces T b) ksTuple Measure.addHaar
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

/-- The K-side local ball at a coefficient is the ball at its ceiling value. -/
theorem ksLocal_ball_eq_ceil (b : Bad (nativePlaceSelection T)) (c : ℝ) (hc : 0 ≤ c) :
    padicFractionalLattice (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
        (K := CommonPrimeCompletion (ksPlace T b)) c =
      padicFractionalLattice (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
        (K := CommonPrimeCompletion (ksPlace T b)) (ksCeilCoeff (l := l) T b c) := by
  unfold ksCeilCoeff
  exact padicFractionalLattice_eq_intCeil (p := (completionRationalPrime (nativeBadToKPlace T b)).val) hc

/-- The constant half coefficient lattice equals the ceiling lattice. -/
theorem urFracConst_eq (b : Bad (nativePlaceSelection T)) :
    arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
        (fun _ => actualRootCoeff (l := l) T b ()) =
      arithmeticTupleFractionalLattice (ksPlaces T b) ksTuple
        (fun _ => urCeilC (l := l) T b) := by
  apply Mzk1URThetaHullTensorActual.arithmeticTupleFractionalLattice_congr
  intro i
  rw [urCeilC_eq (l := l) T b]
  exact ksLocal_ball_eq_ceil (l := l) T b (actualRootCoeff (l := l) T b ())
    (urRootCoeff_nonneg' (l := l) T b)

/-- The label-1 K-side theta region is the ceiling region. -/
theorem urLabelOneRegion_eq_ceilRegion (b : Bad (nativePlaceSelection T)) :
    ksThetaRegion (l := l) T b (oneLabel l) =
      thetaTensorScaledRegion (ksPlaces T b) ksTuple
        (fun _ => urCeilC (l := l) T b) := by
  unfold ksThetaRegion thetaTensorScaledRegion ksThetaCoeff
  rw [urOneLabelCoeff_eq (l := l) T b, urFracConst_eq (l := l) T b]

/-- Exact log-volume of the label-1 K-side theta region. -/
theorem urLabelOneRegion_logVolume (b : Bad (nativePlaceSelection T)) :
    arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        Measure.addHaar (ksThetaRegion (l := l) T b (oneLabel l)) =
      -(urCeilC (l := l) T b * Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)) := by
  rw [urLabelOneRegion_eq_ceilRegion (l := l) T b]
  unfold thetaTensorScaledRegion at ⊢
  exact urCeilRegion_logVolume (l := l) T b




/-- The ceil region as the pure-generator translate of the unit reference. -/
theorem urCeilRegion_eq_smul (b : Bad (nativePlaceSelection T)) :
    (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) : Set (ksBlock T b)) =
      arithmeticTupleFractionalPureGenerator (ksPlaces T b) ksTuple
        (urCeilData (l := l) T b).localGenerator •
        arithmeticTupleCanonicalUnitReference (ksPlaces T b) ksTuple := by
  unfold thetaTensorScaledRegion
  exact arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    (ksPlaces T b) ksTuple (urCeilData (l := l) T b)

/-- The ceil region has positive Haar mass. -/
theorem urCeilRegion_measure_pos (b : Bad (nativePlaceSelection T)) :
    0 < MeasureTheory.Measure.addHaar
      (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) : Set (ksBlock T b)) := by
  rw [urCeilRegion_eq_smul (l := l) T b]
  exact measure_pos_smul_pureGenerator (ksPlaces T b) ksTuple
    (urCeilData (l := l) T b) MeasureTheory.Measure.addHaar

/-- The ceil region has finite Haar mass. -/
theorem urCeilRegion_measure_lt_top (b : Bad (nativePlaceSelection T)) :
    MeasureTheory.Measure.addHaar
      (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
        (fun _ => urCeilC (l := l) T b) : Set (ksBlock T b)) < ⊤ := by
  rw [urCeilRegion_eq_smul (l := l) T b]
  exact measure_lt_top_smul_pureGenerator (ksPlaces T b) ksTuple
    (urCeilData (l := l) T b) MeasureTheory.Measure.addHaar

/-- The ceil region is closed (it is compact). -/
theorem urCeilRegion_isClosed (b : Bad (nativePlaceSelection T)) :
    IsClosed (thetaTensorScaledRegion (places := ksPlaces T b) (tuple := ksTuple)
      (fun _ => urCeilC (l := l) T b) : Set (ksBlock T b)) := by
  rw [urCeilRegion_eq_smul (l := l) T b]
  exact (isCompact_smul_pureGenerator (ksPlaces T b) ksTuple
    (urCeilData (l := l) T b)).isClosed

/-- The label-1 theta region has positive Haar mass. -/
theorem ksLabelOneRegion_measure_pos (b : Bad (nativePlaceSelection T)) :
    0 < MeasureTheory.Measure.addHaar
      (ksThetaRegion (l := l) T b (oneLabel l) : Set (ksBlock T b)) := by
  rw [urLabelOneRegion_eq_ceilRegion (l := l) T b]
  exact urCeilRegion_measure_pos (l := l) T b



#print axioms urOneLabelCoeff_eq
#print axioms urFracConst_eq
#print axioms urLabelOneRegion_eq_ceilRegion
#print axioms urLabelOneRegion_logVolume
#print axioms urCeilC_eq
#print axioms urCeilGenerator_norm
#print axioms urCeilRegion_logVolume
#print axioms urCeilRegion_measure_pos
#print axioms urLabelOneRegion_eq_ceilRegion

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
end
