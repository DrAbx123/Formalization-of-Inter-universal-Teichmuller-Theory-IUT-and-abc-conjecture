/- hlocal 的 by_cases 结构（Lead 2026-11-17 澄清: 不登记 e_eq_one obligation）:
   per v: by_cases e_v: e_v>=2 => ramified branch (delta_abs>=e_v-1 => e_v<=2delta_abs);
          e_v=1 => unramified-at-Q (delta_abs=0 by differentExponent_eq_zero_of_unramified),
          唯一 paper input = (obligation: prop18_support_classification)（s 支撑元素分类: q-支撑 => conductor 覆盖; d-支撑 => 矛盾 ramified）。
   本件给出 by_cases 的纯逻辑合并 + 指向两个分支算术件。 -/
import tmp.sheaf.xif.paper.Mzk1ULHbadProp18Actual
import tmp.sheaf.xif.paper.Mzk1ULHbadHlocalBranchActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalCasesActual

/-- by_cases 合并: e_v>=2 分支与 e_v=1 分支都给 hlocal 界 => 对所有 e_v>=1 成立。 -/
theorem hlocal_by_cases (e : ℕ) (logS logD logF : ℝ)
    (he1 : 1 ≤ e)
    (hram : 2 ≤ e → logS ≤ 2 * (logD + logF))
    (hunr : e = 1 → logS ≤ 2 * (logD + logF)) :
    logS ≤ 2 * (logD + logF) := by
  rcases Nat.lt_or_ge e 2 with hlt | hge
  · have he : e = 1 := by omega
    exact hunr he
  · exact hram hge

/-- ramified 分支: 从 e<=2delta 与 log 归一得 localLogS<=2localLogD（logD=delta*logp）。 -/
theorem ramified_covers (e delta : ℕ) (logp logF : ℝ)
    (he : 2 ≤ e) (hdelta : e - 1 ≤ delta) (hlogp : 0 ≤ logp) (hF : 0 ≤ logF) :
    (e : ℝ) * logp ≤ 2 * ((delta : ℝ) * logp + logF) :=
  LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalBranchActual.hlocal_of_ramified e delta logp logF he hdelta hlogp hF

#print axioms hlocal_by_cases
#print axioms ramified_covers

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalCasesActual
