import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The positive label j = 1 as a ThetaLabel. -/
noncomputable def oneThetaLabel : ThetaLabel (l := l) :=
  ⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩

theorem rootNormedThetaValueInL_one_norm :
    ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) (oneThetaLabel (l := l))) :
      rootNormedExtension T b)‖ = rootNormedElementNorm T b := by
  rw [rootNormedThetaValueInL_norm]
  have h : thetaLabelToSigned (l := l) (oneThetaLabel (l := l)) = oneLabel l := rfl
  rw [h, oneLabel_val]
  norm_num [gaussExponent]
  rfl

theorem rootNormedElementNorm_pow_twoL_eq_p_zpow :
    (rootNormedElementNorm T b) ^ (2 * l.value) =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) := by
  rw [rootNormedElementNorm_pow_twoL]
  change ‖qVFamNormalizedGenerator T b‖ =
    (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b))
  exact qVFamNormalizedGenerator_norm T b

/-- The root element norm is p^(-c_norm/(2l)). -/
theorem rootNormedElementNorm_eq_p_rpow :
    rootNormedElementNorm T b =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) := by
  have hrootpos : 0 < rootNormedElementNorm T b :=
    norm_pos_iff.mpr (rootNormedElement_ne_zero (T := T) (b := b))
  have hp0 : (0 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  have hn : 2 * l.value ≠ 0 := by
    exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hpow := rootNormedElementNorm_pow_twoL_eq_p_zpow (T := T) (b := b)
  have hrpow :
      (Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)))) ^
        (2 * l.value) =
      (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) := by
    calc
      (Real.rpow (qVFamTensorP T b : Real)
          (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)))) ^
          (2 * l.value)
          = (Real.rpow (qVFamTensorP T b : Real)
              (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real)))) ^
              ((2 * l.value : ℕ) : ℝ) := by
            rw [Real.rpow_natCast]
      _ = Real.rpow (qVFamTensorP T b : Real)
            ((-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) *
              ((2 * l.value : ℕ) : ℝ)) := by
            exact (Real.rpow_mul hp0.le _ _).symm
      _ = (qVFamTensorP T b : Real) ^ (-(qVFamNormalizedCoefficient T b)) := by
            congr 1
            norm_num
            have hl : (l.value : Real) ≠ 0 := by
              exact_mod_cast l.prime.ne_zero
            field_simp [hl]
  refine (pow_left_inj₀ hrootpos.le
    (Real.rpow_pos_of_pos hp0 _).le hn).mp ?_
  exact hpow.trans hrpow.symm

theorem rootNormedElementNorm_pos : 0 < rootNormedElementNorm T b :=
  norm_pos_iff.mpr (rootNormedElement_ne_zero (T := T) (b := b))

theorem rootNormedElementNorm_lt_one : rootNormedElementNorm T b < 1 := by
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  have hc : 0 < qVFamNormalizedCoefficient T b :=
    qVFamNormalizedCoefficient_pos T b
  have hn : 2 * l.value ≠ 0 := by
    exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hpow := rootNormedElementNorm_pow_twoL_eq_p_zpow (T := T) (b := b)
  have hlt : (rootNormedElementNorm T b) ^ (2 * l.value) < 1 := by
    rw [hpow]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact (pow_lt_one_iff_of_nonneg (rootNormedElementNorm_pos T b).le hn).mp hlt

theorem rootNormedThetaValueInL_norm_le_rootNorm
    (j : ThetaLabel (l := l)) :
    ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖ ≤ rootNormedElementNorm T b := by
  rw [rootNormedThetaValueInL_norm]
  have hrootpos := rootNormedElementNorm_pos T b
  have hrootlt := rootNormedElementNorm_lt_one T b
  have hg : (1 : ℤ) ≤ gaussExponent (thetaLabelToSigned (l := l) j).1 := by
    have hj : 0 < (thetaLabelToSigned (l := l) j).1 := j.2
    unfold gaussExponent
    nlinarith [sq_nonneg (thetaLabelToSigned (l := l) j).1]
  have hz := zpow_le_zpow_right_of_le_one₀ hrootpos hrootlt.le hg
  simpa [rootNormedElementNorm] using hz

/-- The maximal root image radius is attained at label j = 1. -/
theorem rootImageRadius_eq_rootNorm :
    (rootImageRadius T b : Real) = rootNormedElementNorm T b := by
  apply le_antisymm
  · unfold rootImageRadius
    have hsup : (Finset.univ.sup (fun j : ThetaLabel (l := l) =>
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
            rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal))) ≤
        (⟨rootNormedElementNorm T b, (rootNormedElementNorm_pos T b).le⟩ : NNReal) := by
      apply Finset.sup_le
      intro j _
      exact_mod_cast rootNormedThetaValueInL_norm_le_rootNorm (T := T) (b := b) j
    exact_mod_cast hsup
  · have hge := rootImageRadius_ge (T := T) b (oneThetaLabel (l := l))
    rw [rootNormedThetaValueInL_one_norm] at hge
    exact hge

/-- Closed form: rootImageRadius = p^(-c_norm/(2l)). -/
theorem rootImageRadius_eq_p_rpow :
    (rootImageRadius T b : Real) =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))) := by
  rw [rootImageRadius_eq_rootNorm, rootNormedElementNorm_eq_p_rpow]

end LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual

end
