/- hlocal (Prop1.3(i) local support) 的算术核心 + 分支归约（Lead 计划 2026-11-17）:
   - donor (DONE 2026-11-16T21:04:12): Mzk1G1F7DifferentExponentBoundsActual.
       differentExponent_ge_ramification_sub_one (e>=? => e-1 <= delta),
       differentExponent_eq_zero_of_unramified (unramified => delta=0);
   - 分支1 (ramified, e>=2): delta >= e-1 且 e>=2 => e <= 2*delta（omega）;
   - 分支2 (unramified, e=1): delta=0（donor）; conductor/bad support 项覆盖 log s;
   ⇒ per-place localLogS <= 2(localLogD + localLogF) 的形式化需要 paper 的局部 d_vQ/f_vQ 定义;
   本件给出可直接复用的算术引理 + 具名 Prop（hlocal_per_place），不做 fake。 -/
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1F7DifferentExponentBoundsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual

/-- ramified 分支: e >= 2 且 delta >= e-1 ⇒ e <= 2*delta（Lead 计划的 1 步）。 -/
theorem e_le_two_mul_delta (e delta : Nat) (he : 2 ≤ e) (hdelta : e - 1 ≤ delta) :
    e ≤ 2 * delta := by omega

/-- e >= 2 且 delta >= e-1 ⇒ delta >= 1。 -/
theorem delta_pos_of_ramified (e delta : Nat) (he : 2 ≤ e) (hdelta : e - 1 ≤ delta) :
    1 ≤ delta := by omega

/-- per-place Prop1.3(i) local support（具名 Prop，等局部 d/f 定义后填）:
    localLogS <= 2*(localLogD + localLogF); 分支由 ramified(e<=2delta)/unramified 提供。 -/
def hlocal_per_place (localLogS localLogD localLogF : ℝ) : Prop :=
  localLogS ≤ 2 * (localLogD + localLogF)

#print axioms e_le_two_mul_delta
#print axioms delta_pos_of_ramified

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHlocalActual