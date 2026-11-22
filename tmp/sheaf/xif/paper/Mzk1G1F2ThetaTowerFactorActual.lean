/- U-R C2 / K-side bridge (2/2): tower factors in the forms consumed by the K-side packet.

  Kurt's consumption (C2 K-side): the denominator of `arithmeticTupleNormalizedLogVolume`
  (FinitePlaceNormalizedUnitScalingLogVolume.lean:92) is
  `Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)`, whose single factor is
  `[K_w : ℚ_p] = finrank ℚ_[p] (CommonPrimeCompletion (ksPlace T b))`, while the Fmod-side
  weight is `lamWeight b = finrank ℚ_[p_v] (NormalizedCompletion b.1)`.
  The needed identities are
    (i)  `[K_w : ℚ_p] = [K_w : (Fmod)_v] * [(Fmod)_v : ℚ_p]` (tower factor), and
    (ii) `(1/[K_w : ℚ_p]) * [K_w : (Fmod)_v] = 1/[(Fmod)_v : ℚ_p]` (normalized-volume conversion).
  Both are proved here abstractly (`Module.finrank_mul_finrank` + field arithmetic); they are
  instantiated by taking `Fv := NormalizedCompletion (b.1)`, `Kw := NormalizedCompletion (ksPlace T b)`
  (the completion is `ksPlace`'s own completion -- no extra completion isomorphism is needed, per
  kurt: `ThetaK` places must be `ksPlace`; the remaining data bridge is `T.arithmetic.K = ThetaK`).
  No sorry/axiom. -/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTowerFactorActual

/-- **tower factor**：`[Kw : ℚ_p] = [Kw : Fv] * [Fv : ℚ_p]`（`Module.finrank_mul_finrank`）。 -/
theorem tower_factor_finrank {p : ℕ} [Fact p.Prime] (Fv Kw : Type*)
    [Field Fv] [Field Kw] [Algebra ℚ_[p] Fv] [Algebra Fv Kw] [Algebra ℚ_[p] Kw]
    [IsScalarTower ℚ_[p] Fv Kw] [FiniteDimensional ℚ_[p] Fv] [FiniteDimensional Fv Kw] :
    Module.finrank ℚ_[p] Kw = Module.finrank Fv Kw * Module.finrank ℚ_[p] Fv :=
  Module.finrank_mul_finrank ℚ_[p] Fv Kw

/-- **归一化换算**：`(1/[Kw:ℚ_p]) * [Kw:Fv] = 1/[Fv:ℚ_p]`（K/Fmod 的 normalized log-volume 因子）。 -/
theorem tower_factor_normalization {p : ℕ} [Fact p.Prime] (Fv Kw : Type*)
    [Field Fv] [Field Kw] [Algebra ℚ_[p] Fv] [Algebra Fv Kw] [Algebra ℚ_[p] Kw]
    [IsScalarTower ℚ_[p] Fv Kw] [FiniteDimensional ℚ_[p] Fv] [FiniteDimensional Fv Kw]
    (hF : 0 < Module.finrank ℚ_[p] Fv) (hK : 0 < Module.finrank Fv Kw) :
    (1 / (Module.finrank ℚ_[p] Kw : ℝ)) * (Module.finrank Fv Kw : ℝ) =
      1 / (Module.finrank ℚ_[p] Fv : ℝ) := by
  have hfin := tower_factor_finrank (p := p) Fv Kw
  have hF' : (0 : ℝ) < (Module.finrank ℚ_[p] Fv : ℝ) := by exact_mod_cast hF
  have hK' : (0 : ℝ) < (Module.finrank Fv Kw : ℝ) := by exact_mod_cast hK
  rw [hfin]
  push_cast
  field_simp

#print axioms tower_factor_finrank
#print axioms tower_factor_normalization

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaTowerFactorActual
