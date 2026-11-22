/- hlocal per-place 的实例化（修正语义: e_v = Fmod/Ftpd 在 v 上对 Q_p 的分歧指数, 不是 F/Fmod 的）:
   **禁止用 Sum f = [K:Q]**，除非 p 在 Fmod/Q 完全非分歧; 一般用 Sum e f = [K:Q] 与 e-权。
   p∉{2,3,5,l} 只给 Fmod/Ftpd? 实际上是 F/Fmod 及 Ftpd/Fmod unramified; Fmod/Q 仍可在 bad moduli p 分歧。
   分支: (i) e_v>=2 ⇒ ramified: delta_abs(Ftpd/Q at w) >= e_v-1（因 e(Ftpd/Fmod)=1 at p）⇒ e_v <= 2 delta_abs;
         (ii) e_v=1 ⇒ Q-层 unramified ⇒ delta_abs=0，conductor/bad support 项覆盖 log s（逐位检查）。
   原注释:
   unramified: log s = log p = log f（fiber_sum / sum_localLogF_fiber_eq_finrank）⇒ localLogS <= 2(0+localLogF);
   ramified: e<=2delta ⇒ e·logp <= 2(delta·logp) <= 2(delta·logp + logF);
   域: K = Fmod (s 侧) / Ftpd (d,f 侧); unramified p 时两边 fiber 满 ⇒ 归一后都是 log p。
   donor: Mzk1ULHbadHlocalBranchActual.{ramified_branch,unramified_branch,hlocal_of_ramified};
   Mzk1ULHbadHlocalInstantiationActual.sum_localLogF_fiber_eq_finrank。 -/
import tmp.sheaf.xif.paper.Mzk1ULHbadHlocalBranchActual
import tmp.sheaf.xif.paper.Mzk1ULHbadHlocalInstantiationActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalPerPlaceActual

open LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalBranchActual

/-- unramified 分支实例: log s_vQ = log p, localLogD=0, localLogF=log p ⇒ hlocal_per_place。 -/
/-- unramified 分支: e_v=1 ⇒ delta_abs=0（donor）; 若 conductor 项覆盖 log s（bad support）则 hlocal 成立。 -/
theorem hlocal_unramified_inst (p : ℕ) (logF : ℝ) (hlogp : 0 ≤ Real.log (p : ℝ))
    (hcover : Real.log (p : ℝ) ≤ logF) (hF : 0 ≤ logF) :
    Real.log (p : ℝ) ≤ 2 * ((0 : ℝ) + logF) := by
  linarith

/-- ramified 分支实例（localLogF 项非负）: e·logp <= 2(delta·logp+logF)。 -/
theorem hlocal_ramified_inst (e delta : ℕ) (logp logF : ℝ)
    (he : 2 ≤ e) (hdelta : e - 1 ≤ delta) (hlogp : 0 ≤ logp) (hF : 0 ≤ logF) :
    (e : ℝ) * logp ≤ 2 * ((delta : ℝ) * logp + logF) :=
  hlocal_of_ramified e delta logp logF he hdelta hlogp hF

/-- deg_E 归一后的 localLogF_vQ = log p（fiber 满）。 -/
theorem localLogF_vQ_eq_logp (K : Type*) [Field K] [NumberField K]
    {S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))} (p : ℕ)
    (hp : ∀ P ∈ S, (LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs = p)
    (hsum : (∑ P ∈ S, ((P : Ideal (𝓞 K)).inertiaDeg ℤ : ℝ)) = (Module.finrank ℚ K : ℝ)) :
    (∑ P ∈ S, LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual.localLogF K P) =
      (Module.finrank ℚ K : ℝ) * Real.log (p : ℝ) :=
  LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalInstantiationActual.sum_localLogF_fiber_eq_finrank K p hp hsum

#print axioms hlocal_unramified_inst
#print axioms hlocal_ramified_inst
#print axioms localLogF_vQ_eq_logp

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalPerPlaceActual