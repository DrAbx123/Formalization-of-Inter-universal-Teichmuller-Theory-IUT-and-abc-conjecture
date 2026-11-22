/- hlocal 的两分支 per-place 引理（ramified: e<=2delta; unramified: delta=0 + conductor 覆盖）
   纯实数/整数算术，接 Mzk1ULHbadHlocalActual.e_le_two_mul_delta 与
   Mzk1G1F7DifferentExponentBoundsActual.differentExponent_eq_zero_of_unramified。
   目标形式: localLogS <= 2*(localLogD + localLogF)（hlocal_per_place）。 -/
import tmp.sheaf.xif.paper.Mzk1ULHbadHlocalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalBranchActual

open LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalActual

/-- ramified 分支: localLogS = e*logp, localLogD = delta*logp, e<=2delta, logp>=0
    ⇒ localLogS <= 2*localLogD。 -/
theorem ramified_branch (e delta : Nat) (logp : ℝ)
    (he : 2 ≤ e) (hdelta : e - 1 ≤ delta) (hlogp : 0 ≤ logp) :
    (e : ℝ) * logp ≤ 2 * ((delta : ℝ) * logp) := by
  have he2 : e ≤ 2 * delta := e_le_two_mul_delta e delta he hdelta
  have hcast : (e : ℝ) ≤ 2 * (delta : ℝ) := by exact_mod_cast he2
  nlinarith [hlogp, hcast]

/-- unramified 分支: delta=0 ⇒ localLogD=0; conductor 覆盖 log s ⇒ localLogS <= 2*localLogF。 -/
theorem unramified_branch (logS logF : ℝ) (hcover : logS ≤ logF) (hF : 0 ≤ logF) :
    logS ≤ 2 * ((0 : ℝ) + logF) := by
  linarith

/-- 两分支合并形式（抽象 per-place）: 若 localLogD=delta*logp, localLogS=e*logp 且 e<=2delta,
    则 hlocal_per_place 成立（localLogF >= 0）。 -/
theorem hlocal_of_ramified (e delta : Nat) (logp logF : ℝ)
    (he : 2 ≤ e) (hdelta : e - 1 ≤ delta) (hlogp : 0 ≤ logp) (hF : 0 ≤ logF) :
    (e : ℝ) * logp ≤ 2 * ((delta : ℝ) * logp + logF) := by
  have h := ramified_branch e delta logp he hdelta hlogp
  linarith

/-- 两分支合并形式（unramified）: logS <= logF ⇒ hlocal_per_place（localLogD=0）。 -/
theorem hlocal_of_unramified (logS logF : ℝ) (hcover : logS ≤ logF) (hF : 0 ≤ logF) :
    logS ≤ 2 * ((0 : ℝ) + logF) := unramified_branch logS logF hcover hF

#print axioms ramified_branch
#print axioms unramified_branch
#print axioms hlocal_of_ramified
#print axioms hlocal_of_unramified

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalBranchActual
