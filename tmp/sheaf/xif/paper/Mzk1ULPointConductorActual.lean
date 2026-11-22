/- point-field conductor N_D(λ)（paper：N_D(λ) 域 = ℚ(λ) = Fmod，归一 [ℚ(λ):Q]）。

pointField lam := IntermediateField.adjoin ℚ {lam}（⊆ K_V）; pointND lam :=
truncConductor (K := pointField lam) ⟨lam, _⟩（per-place truncated conductor:
support = λ/1−λ/λ^{-1} 的坏位，见 Mzk1G1LocalHeightCriterionActual.IsBadPlace）。

cross-field 不等式 log f_Ftpd ≤ pointND lam 需要 F_tpd(λ) 与 f_Ftpd 的实际 producer
（route §6.2: 从 λ 取 Legendre 曲线的 actual T）; tree 里目前没有 λ→SourceNativeInitialThetaData
的 producer（Mzk1InitialThetaDataMappingAuditActual:35 明说 initialThetaDataOfSource 未完成），
故本文件只落 pointND 的实际定义与非负性，cross-field 不等式按三段报给 Lead。 -/
import Mathlib.Tactic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import tmp.sheaf.xif.paper.Mzk1G1LocalHeightCriterionActual

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual

open LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual
open NumberField

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- 点域 ℚ(λ)。 -/
def pointField (lam : K) : IntermediateField ℚ K := IntermediateField.adjoin ℚ {lam}

/-- λ 作为点域元素。 -/
def pointElem (lam : K) : ↥(pointField lam) :=
  ⟨lam, (IntermediateField.subset_adjoin (F := ℚ) (S := {lam})) (Set.mem_singleton lam)⟩

/-- 点域是 number field（lam 在 NumberField 中整）。 -/
theorem pointField_finiteDimensional (lam : K) :
    FiniteDimensional ℚ ↥(pointField lam) :=
  IntermediateField.adjoin.finiteDimensional
    (Algebra.IsAlgebraic.isAlgebraic lam).isIntegral

/-- pointField 的 NumberField 实例。 -/
instance pointFieldNumberField (lam : K) : NumberField ↥(pointField lam) :=
  { to_charZero := inferInstance
    to_finiteDimensional := pointField_finiteDimensional lam }

/-- paper 的 N_D(λ)（ℚ(λ) 域，归一 [ℚ(λ):Q]）。 -/
noncomputable def pointND (lam : K) : ℝ :=
  truncConductor (K := ↥(pointField lam)) (pointElem lam)

/-- pointND 非负。 -/
theorem pointND_nonneg (lam : K) : 0 ≤ pointND lam :=
  truncConductor_nonneg (K := ↥(pointField lam)) (pointElem lam)

end LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual