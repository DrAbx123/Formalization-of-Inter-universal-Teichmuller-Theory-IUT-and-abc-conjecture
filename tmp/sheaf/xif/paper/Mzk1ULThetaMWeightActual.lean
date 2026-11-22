/- θ_M 权重 / eFiber（Lead THETA-M-UNIT-AUDIT a/b/c 的 Lean 接口）:
  eFiber b := ramificationIdx of nativeBadToFPlace b over b.1（F/Fmod 局部 e）。
  thetaMWeight b := 1/(lamWeight b * eFiber b)（lamWeight=[Fmod_b:Q_p]=ef）。
  thetaMWeight * thetaLamWeight = 1/(eFiber * dModF)（d_mod 在分母）。
  V_M per-item: (-ksCeilC/eFiber + ksDifferentOrder + 1)*logp + exc（仅 q 项除 e_P）。 -/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULThetaMWeightActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Module.Finite (𝓞 (T.arithmetic.Fmod)) (𝓞 (T.arithmetic.F))]

/-- F/Fmod 在 b 上的局部 ramification index（eFiber）。 -/
noncomputable def eFiber (b : Bad (nativePlaceSelection T)) : ℕ :=
  ((nativeBadToFPlace T b).maximalIdeal.asIdeal).ramificationIdx (𝓞 (T.arithmetic.Fmod))

/-- eFiber 正。 -/
theorem eFiber_pos (b : Bad (nativePlaceSelection T)) : 0 < eFiber (T := T) b := by
  unfold eFiber
  exact Ideal.ramificationIdx_pos (R := 𝓞 (T.arithmetic.Fmod))
    (q := (nativeBadToFPlace T b).maximalIdeal.asIdeal)

/-- θ_M 权重: 1/(λ_b·e_P)。 -/
noncomputable def thetaMWeight (b : Bad (nativePlaceSelection T)) : ℝ :=
  1 / (lamWeight T b * (eFiber (T := T) b : ℝ))

/-- θ_M·λ/d_mod = 1/(e_P·d_mod)（d_mod 在分母）。 -/
theorem thetaMWeight_mul_thetaLamWeight (b : Bad (nativePlaceSelection T)) :
    thetaMWeight T b * thetaLamWeight T b = 1 / ((eFiber (T := T) b : ℝ) * dModF T) := by
  unfold thetaMWeight thetaLamWeight
  have hlam : lamWeight T b ≠ 0 := by
    have hpos : (0 : ℝ) < lamWeight T b := by
      unfold lamWeight
      exact_mod_cast Module.finrank_pos
    exact ne_of_gt hpos
  have he : (eFiber (T := T) b : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (eFiber_pos T b)
  have hd : dModF T ≠ 0 := ne_of_gt (dModF_pos T)
  field_simp

/-- V_M 的 per-item 形式（仅 q 项除 e_P; different/exceptional 保持）。 -/
noncomputable def urPacketV_K_M (b : Bad (nativePlaceSelection T)) : ℝ :=
  (-(ksCeilC (l := l) T b) / (eFiber (T := T) b : ℝ) +
      ksDifferentOrder (l := l) T b + 1) * ksLogP T b +
    ksExceptionalSum (l := l) T b

end LeanFormal.IUT.XiFPaper.Mzk1ULThetaMWeightActual