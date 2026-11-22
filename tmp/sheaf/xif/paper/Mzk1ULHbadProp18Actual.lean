/- hlocal 的两个 paper input 作为具名义务（Lead 2026-11-17）:
   (obligation: prop18_support_classification) -- D6/Prop1.8: p∉{2,3,5,l} 时 Vdst_Q ⊆ image Supp(q_Ftpd + d_Ftpd);
   (obligation: conductor_covers_qsupport)   -- bad(q)-support 时 conductor 局部系数覆盖 s 项（log s_p <= log f_p）。
   本件把它们写成显式 Prop 并给出 ⇒ hlocal 求和界的结构推理（无 fake）。
   算术分支（ramified e<=2δ / unramified δ=0）已在 Mzk1ULHbadHlocalBranchActual 闭合。 -/
import tmp.sheaf.xif.paper.Mzk1ULHbadHlocalBranchActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadProp18Actual

/-- 具名义务 (prop18_support_classification): dst ⊆ q ∪ d（p 非 special）。 -/
def prop18_support_classification (dst q d : Finset ℕ) : Prop :=
  dst ⊆ q ∪ d

/-- 具名义务 (conductor_covers_qsupport): q-support 的 s 项被 conductor 覆盖。 -/
def conductor_covers_qsupport (q : Finset ℕ) (logS logF : ℕ → ℝ) : Prop :=
  ∀ p, p ∈ q → logS p ≤ logF p

/-- d-support（ramified）的 s 项被 2*logD 覆盖（由 ramified 分支提供）。 -/
def different_bound_dsupport (d : Finset ℕ) (logS logD : ℕ → ℝ) : Prop :=
  ∀ p, p ∈ d → logS p ≤ 2 * logD p

/-- 结构推理: 三个义务 ⇒ hlocal 的求和界 Σ dst logS ≤ 2(Σ logD + Σ logF)。
    (给定 logD, logF 非负; dst⊆q∪d 时逐点选择 q 或 d 分支。) -/
theorem hlocal_sum_of_obligations (dst q d : Finset ℕ)
    (logS logD logF : ℕ → ℝ)
    (h18 : prop18_support_classification dst q d)
    (hq : conductor_covers_qsupport q logS logF)
    (hd : different_bound_dsupport d logS logD)
    (hD0 : ∀ p, 0 ≤ logD p) (hF0 : ∀ p, 0 ≤ logF p) :
    (∑ p ∈ dst, logS p) ≤
      2 * ((∑ p ∈ dst, logD p) + (∑ p ∈ dst, logF p)) := by
  have hpt : ∀ p ∈ dst, logS p ≤ 2 * (logD p + logF p) := by
    intro p hp
    have hmem : p ∈ q ∪ d := h18 hp
    rw [Finset.mem_union] at hmem
    rcases hmem with hpq | hpd
    · have h1 := hq p hpq
      have h2 := hF0 p
      have h3 := hD0 p
      linarith
    · have h1 := hd p hpd
      have h2 := hF0 p
      linarith
  have hsum : (∑ p ∈ dst, logS p) ≤ ∑ p ∈ dst, 2 * (logD p + logF p) :=
    Finset.sum_le_sum hpt
  calc (∑ p ∈ dst, logS p)
      ≤ ∑ p ∈ dst, 2 * (logD p + logF p) := hsum
    _ = 2 * ((∑ p ∈ dst, logD p) + (∑ p ∈ dst, logF p)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib]

#print axioms hlocal_sum_of_obligations

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadProp18Actual
