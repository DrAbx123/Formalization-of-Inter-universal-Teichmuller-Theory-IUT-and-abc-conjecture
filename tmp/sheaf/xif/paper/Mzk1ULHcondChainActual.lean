/- hcond 链设计骨架（不等 Legendre 相等定理；显式参数接口）:
  paper L618 / route L615-621: log f_Ftpd ≤ N_D(lam)（域 Q(lam)，归一 [Q(lam):Q]）。
  Legendre 判别式 16λ²(1−λ)² ⇒ 坏约化位 ⊆ {λ/1−λ bad} ∪ {2}（split multiplicative 例外 2）。
  该文件先用 LegendreTpdSupport 结构把逐位数据/常数显式化; 等 Legendre 相等与逐位证明落地后
  用 hcond_after_absorb 输出 hcond。所有数值关系显式，不引入假对象。 -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHcondChainActual

/-- hcond 的逐位/常数数据（Legendre 情形）:
  logFtpd = Σ_{bad TPD p} f_p log p /[F_tpd:Q]; logPointND = N_D(lam)（点域）;
  log2Const 为把 {2} 位并入点域 truncation 的常数项（≤ log 2）。 -/
structure LegendreTpdSupport where
  /-- log f_Ftpd（paper L618 LHS）。 -/
  logFtpd : ℝ
  /-- 点域 truncated conductor N_D(lam)（不含 2 的位）。 -/
  logPointND : ℝ
  /-- 2-位的常数吸收项（≤ log 2）。 -/
  log2Const : ℝ
  /-- 逐位比较后的主不等式（由 support 包含 + 逐位 f_P/[F_tpd:Q] 对齐给）。 -/
  perPlace_bound : logFtpd ≤ logPointND + log2Const
  /-- log2Const ≤ log 2（2 的局部导子/不同贡献）。 -/
  log2Const_le : log2Const ≤ Real.log 2

/-- 吸收 2-位后的 hcond 形状: log f_Ftpd ≤ N_D(lam) + log 2。 -/
theorem hcond_after_absorb (D : LegendreTpdSupport) :
    D.logFtpd ≤ D.logPointND + Real.log 2 :=
  le_trans D.perPlace_bound (add_le_add_right D.log2Const_le D.logPointND)

/-- 若点域 N_D 已包含 2 位（logPointND := N_D + log2Const 时的定义），则 hcond 直接给出。 -/
theorem hcond_with_two (D : LegendreTpdSupport) :
    D.logFtpd ≤ D.logPointND + Real.log 2 :=
  hcond_after_absorb D

/-- 逐位 support 包含的数据层: (TPD bad ⊆ qSupport∪{2}) 与 (qSupport ⊆ pointBad∪{2})。 -/
structure LegendreSupportIncl where
  qSupport : Finset ℕ
  tpdBadPrimes : Finset ℕ
  pointBadPrimes : Finset ℕ
  tpd_subset : tpdBadPrimes ⊆ qSupport ∪ {2}
  q_subset_point : qSupport ⊆ pointBadPrimes ∪ {2}

/-- support 包含的传递: TPD bad ⊆ pointBad ∪ {2}。 -/
theorem tpd_subset_point_of (D : LegendreSupportIncl) :
    D.tpdBadPrimes ⊆ D.pointBadPrimes ∪ {2} := by
  intro p hp
  have h1 := D.tpd_subset hp
  simp only [Finset.mem_union, Finset.mem_singleton] at h1 ⊢
  rcases h1 with hq | h2
  · have := D.q_subset_point hq
    simp only [Finset.mem_union, Finset.mem_singleton] at this
    rcases this with hp' | h2'
    · exact Or.inl hp'
    · exact Or.inr h2'
  · exact Or.inr h2

#print axioms hcond_after_absorb
#print axioms tpd_subset_point_of

end LeanFormal.IUT.XiFPaper.Mzk1ULHcondChainActual