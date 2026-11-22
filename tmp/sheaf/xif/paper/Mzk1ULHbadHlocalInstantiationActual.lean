/- hlocal 实例化的定义层事实（用 sophie 的 DONE localLogF + 我 hlocal 分支算术）:
   unramified fiber: 每 P 的 under 生成元 natAbs = p ⇒ localLogF P = f_P·log p;
   故 Sum localLogF = (Sum f_P)·log p；若 Sum f_P = [K:Q]（unramified 满 fiber）⇒ = [K:Q]·log p;
   除以 deg_E 分母 Sum f_P 得局部 log f_vQ = log p（fiber 归一后）。
   这把 'localLogF <= ...' 的 deg_E 归一与 hlocal 分支算术接上（unramified 分支: log s = log p = log f）。 -/
import tmp.sheaf.xif.paper.Mzk1ULLocalConductorDegActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalInstantiationActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

variable (K : Type*) [Field K] [NumberField K]

/-- fiber 内 under 生成元全为 p ⇒ Sum localLogF = (Sum f_P)·log p。 -/
theorem sum_localLogF_fiber_eq {S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    (p : ℕ) (hp : ∀ P ∈ S, (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs = p) :
    (∑ P ∈ S, localLogF K P) =
      (∑ P ∈ S, ((P : Ideal (𝓞 K)).inertiaDeg ℤ : ℝ)) * Real.log (p : ℝ) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  unfold localLogF
  rw [hp P hP]

/-- unramified 满 fiber（Sum f_P = [K:Q]）⇒ Sum localLogF = [K:Q]·log p。 -/
theorem sum_localLogF_fiber_eq_finrank {S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))}
    (p : ℕ) (hp : ∀ P ∈ S, (underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs = p)
    (hsum : (∑ P ∈ S, ((P : Ideal (𝓞 K)).inertiaDeg ℤ : ℝ)) = (Module.finrank ℚ K : ℝ)) :
    (∑ P ∈ S, localLogF K P) = (Module.finrank ℚ K : ℝ) * Real.log (p : ℝ) := by
  rw [sum_localLogF_fiber_eq K p hp, hsum]

/-- deg_E 归一后（分母 Sum f_P）：局部 log f_vQ = log p。 -/
theorem localLogF_degE_eq_logp (p : ℕ) (sump : ℝ) (hsump : sump ≠ 0) :
    (sump * Real.log (p : ℝ)) / sump = Real.log (p : ℝ) :=
  mul_div_cancel_left₀ _ hsump

#print axioms sum_localLogF_fiber_eq
#print axioms sum_localLogF_fiber_eq_finrank
#print axioms localLogF_degE_eq_logp

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalInstantiationActual
