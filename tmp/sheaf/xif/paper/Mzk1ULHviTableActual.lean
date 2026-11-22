/- U-C Step (viii) (beta): hviTable 的纯 paper 字母记账（平均/加权聚合层）。
   依赖: StepVProcessionAverage donor (collectionBound/processionAverage_le),
   Mzk1ULStepVIPacketAggregationActual (alpha 的 s3014 加权聚合形状),
   S3014StepVProcessionAverageActual (S3014PerLabelBound/AverageBound 定义)。
   本文件只证不依赖具体字母取值的会计层; 字母字典 (d_i->D, exc->S/T, q->Q) 的
   精确匹配在后续 Mzk1ULHviTableLettersActual 里补。 -/
import tmp.sheaf.xif.paper.Mzk1ULStepVIPacketAggregationActual
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Finset
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHviTableActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- (beta-1) 归一化 bad-place 加权平均不超过共同上界: 若每个 packet 的
procession 平均 B b 都不超过同一上界 C + arch, 且 bad-place 权非负、总和为 1,
则加权聚合不超过 C + arch. -/
theorem badWeighted_le_commonBound {ι : Type*} [Fintype ι] (γ B : ι → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : (∑ i, γ i) = 1) {C arch : ℝ}
    (hB : ∀ i, B i ≤ C + arch) :
    (∑ i, γ i * B i) ≤ C + arch := by
  calc (∑ i, γ i * B i) ≤ ∑ i, γ i * (C + arch) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i) (hγ0 i)
    _ = (∑ i, γ i) * (C + arch) := by rw [Finset.sum_mul]
    _ = C + arch := by rw [hγ1, one_mul]

/-- (beta-2) L1701-1783 的平均步骤: 逐标签上界推出进程归一化平均上界. -/
theorem processionAverage_le_of_perLabel (n : ℕ) (hn : 1 ≤ n) (V : ℕ → ℝ)
    {C arch : ℝ} (h : ∀ j ∈ Finset.Icc 1 n, V j ≤ C + arch) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, V j) ≤ C + arch := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ j ∈ Finset.Icc 1 n, V j) ≤ ∑ _j ∈ Finset.Icc 1 n, (C + arch) :=
    Finset.sum_le_sum h
  have hcard : (Finset.Icc 1 n).card = n := by simp
  have hconst : (∑ _j ∈ Finset.Icc 1 n, (C + arch)) = (n : ℝ) * (C + arch) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  calc (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, V j)
      ≤ (1 / (n : ℝ)) * ((n : ℝ) * (C + arch)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hsum, hconst]
    _ = C + arch := by field_simp

/-- (beta-3) hviTable 的会计层: 若 s3014 是 bad-place 加权聚合
sum_b γ b * B b, 每个 packet 的进程平均 B b 都不超过
(1/n) * sum_j collectionBound (2n+1) D Q S T j + arch, 且 γ 归一化,
则 hviTable 成立. 字母字典 (D=logDK, Q=Q, S=logSQ, T=lstar) 见后续文件. -/
theorem hviTable_of_packetBounds {ι : Type*} [Fintype ι] (γ B : ι → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : (∑ i, γ i) = 1)
    (n : ℕ) (hn : 2 ≤ n) (D Q S T arch : ℝ)
    (hB : ∀ i, B i ≤ (1 / (n : ℝ)) *
      (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1) D Q S T j) + arch) :
    (∑ i, γ i * B i) ≤ (1 / (n : ℝ)) *
      (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1) D Q S T j) + arch :=
  badWeighted_le_commonBound γ B hγ0 hγ1 hB

/-- (beta-4) 逐标签版本: s3014 直接以进程平均定义 (1/n) * sum_j V j 时,
由逐标签的 collection-bound 比较得 hviTable 会计层. -/
theorem hviTable_of_perLabelBounds (n : ℕ) (hn : 2 ≤ n) (V : ℕ → ℝ)
    (D Q S T arch : ℝ)
    (hV : ∀ j ∈ Finset.Icc 1 n,
      V j ≤ collectionBound (2 * (n : ℝ) + 1) D Q S T j + arch) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, V j) ≤
      (1 / (n : ℝ)) *
        (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1) D Q S T j) + arch := by
  have h1 : (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, V j) ≤
      (1 / (n : ℝ)) *
        (∑ j ∈ Finset.Icc 1 n, (collectionBound (2 * (n : ℝ) + 1) D Q S T j + arch)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum hV
  have h2 : (∑ j ∈ Finset.Icc 1 n,
        (collectionBound (2 * (n : ℝ) + 1) D Q S T j + arch)) =
      (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1) D Q S T j) +
        (n : ℝ) * arch := by
    rw [Finset.sum_add_distrib, Finset.sum_const]
    have hc : (Finset.Icc 1 n).card = n := by simp
    rw [hc, nsmul_eq_mul]
  calc (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, V j)
      ≤ (1 / (n : ℝ)) * ((∑ j ∈ Finset.Icc 1 n,
          collectionBound (2 * (n : ℝ) + 1) D Q S T j) + (n : ℝ) * arch) := by
        rw [← h2]; exact h1
    _ = (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
          collectionBound (2 * (n : ℝ) + 1) D Q S T j) + arch := by
        field_simp


/-- (beta-5) assembly: per-bad-place per-label pointwise comparison (paper Step (v)/(vi)
字母版本) ⇒ bad-place weighted hviTable 形状. arch 逐 packet 合并为 sum_b gamma_b * arch_b. -/
theorem hviTable_of_badSum_perLabel {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : (∑ i, γ i) = 1)
    (n : ℕ) (hn : 2 ≤ n) (D Q S T : ℝ) (V : ι → ℕ → ℝ) (arch : ι → ℝ)
    (hV : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      V i label ≤ collectionBound (2 * (n : ℝ) + 1) D Q S T label + arch i) :
    (∑ i, γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label))) ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1) D Q S T j) +
        (∑ i, γ i * arch i) := by
  have hb : ∀ i, (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label) ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1) D Q S T j) + arch i :=
    fun i => hviTable_of_perLabelBounds n hn (V i) D Q S T (arch i) (hV i)
  set C : ℝ := (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
    collectionBound (2 * (n : ℝ) + 1) D Q S T j) with hC
  calc (∑ i, γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label)))
      ≤ ∑ i, γ i * (C + arch i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (by simpa [hC] using hb i) (hγ0 i)
    _ = ∑ i, (γ i * C + γ i * arch i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = (∑ i, γ i) * C + ∑ i, γ i * arch i := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
          collectionBound (2 * (n : ℝ) + 1) D Q S T j) + (∑ i, γ i * arch i) := by
        rw [hγ1, one_mul, hC]

#print axioms hviTable_of_badSum_perLabel


/-- (beta-9) 非归一 bad 加权 helper（供 paper 允许 c=Σγ 进 RHS 时使用）：
若每项 B_b ≤ C + arch，则 Σ_b γ_b·B_b ≤ (Σ_b γ_b)·(C + arch)（c=Σγ 显式因子）。 -/
theorem badWeighted_le_commonBound_gen {ι : Type*} [Fintype ι] (γ B : ι → ℝ)
    (hγnn : ∀ i, 0 ≤ γ i) {C arch : ℝ} (hB : ∀ i, B i ≤ C + arch) :
    (∑ i, γ i * B i) ≤ (∑ i, γ i) * (C + arch) := by
  calc (∑ i, γ i * B i) ≤ ∑ i, γ i * (C + arch) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i) (hγnn i)
    _ = (∑ i, γ i) * (C + arch) := by rw [Finset.sum_mul]

#print axioms badWeighted_le_commonBound_gen

#print axioms badWeighted_le_commonBound
#print axioms processionAverage_le_of_perLabel
#print axioms hviTable_of_packetBounds
#print axioms hviTable_of_perLabelBounds



/-- (beta-6) donor collectionBound 对字母 (D,Q,S,T) 的线性性：bad 加权后等价于
加权平均字母的 collectionBound（同 label 系数）。 -/
theorem badWeighted_collectionBound {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (l : ℝ) (j : ℕ) (D Q S T : ι → ℝ) :
    (∑ i, γ i * collectionBound l (D i) (Q i) (S i) (T i) j) =
      collectionBound l (∑ i, γ i * D i) (∑ i, γ i * Q i) (∑ i, γ i * S i)
        (∑ i, γ i * T i) j := by
  unfold collectionBound
  simp_rw [show ∀ i, γ i * (((j : ℝ) + 1) * D i - (j : ℝ) ^ 2 / (2 * l) * Q i
        + S i + 4 * ((j : ℝ) + 1) * T i) =
      ((j : ℝ) + 1) * (γ i * D i) - ((j : ℝ) ^ 2 / (2 * l)) * (γ i * Q i)
        + γ i * S i + (4 * ((j : ℝ) + 1)) * (γ i * T i) from fun i => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  try ring

/-- (beta-7) 最终 hviTable（(i) 裁决形式）：逐 bad place 的 per-label 比较
（字母 D_b,Q_b,S_b,T_b 可随 b 变）⇒ bad 加权聚合以加权平均字母为界。 -/
theorem hviTable_of_collectionLayer {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : (∑ i, γ i) = 1)
    (n : ℕ) (hn : 2 ≤ n) (D Q S T : ι → ℝ) (V : ι → ℕ → ℝ) (arch : ι → ℝ)
    (hV : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      V i label ≤ collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) label + arch i) :
    (∑ i, γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label))) ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (∑ i, γ i * D i) (∑ i, γ i * Q i)
          (∑ i, γ i * S i) (∑ i, γ i * T i) j) + (∑ i, γ i * arch i) := by
  have hb : ∀ i, (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label) ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j) + arch i :=
    fun i => hviTable_of_perLabelBounds n hn (V i) (D i) (Q i) (S i) (T i) (arch i) (hV i)
  have h2 : (∑ i, γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label))) ≤
      (∑ i, γ i * ((1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j))) +
        (∑ i, γ i * arch i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := mul_le_mul_of_nonneg_left (hb i) (hγ0 i)
    calc γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label))
        ≤ γ i * ((1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
            collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j) + arch i) := this
      _ = γ i * ((1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
            collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j)) + γ i * arch i := by
          ring
  have hswap : (∑ i, γ i * ((1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
      collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j))) =
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (∑ i, γ i * D i) (∑ i, γ i * Q i)
          (∑ i, γ i * S i) (∑ i, γ i * T i) j) := by
    have step1 : (∑ i, γ i * ((1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j))) =
        (1 / (n : ℝ)) * (∑ i, γ i * (∑ j ∈ Finset.Icc 1 n,
          collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have step2 : (∑ i, γ i * (∑ j ∈ Finset.Icc 1 n,
          collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j)) =
        (∑ j ∈ Finset.Icc 1 n, ∑ i, γ i *
          collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have step3 : (∑ j ∈ Finset.Icc 1 n, ∑ i, γ i *
          collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (S i) (T i) j) =
        (∑ j ∈ Finset.Icc 1 n, collectionBound (2 * (n : ℝ) + 1)
          (∑ i, γ i * D i) (∑ i, γ i * Q i) (∑ i, γ i * S i) (∑ i, γ i * T i) j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact badWeighted_collectionBound γ (2 * (n : ℝ) + 1) j D Q S T
    rw [step1, step2, step3]
  linarith [h2, hswap]


/-- (beta-8) (i) 裁决实例：S 槽取 Real.log p 时，ΣγS = log p（用 Σγ=1），
bad 加权聚合给出 hviTable 形状（S 槽 = Real.log p）。 -/
theorem hviTable_of_collectionLayer_logp {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i) (hγ1 : (∑ i, γ i) = 1)
    (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (D Q T : ι → ℝ) (V : ι → ℕ → ℝ) (arch : ι → ℝ)
    (hV : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      V i label ≤ collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (Real.log (p : ℝ)) (T i) label
        + arch i) :
    (∑ i, γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, V i label))) ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (∑ i, γ i * D i) (∑ i, γ i * Q i)
          (Real.log (p : ℝ)) (∑ i, γ i * T i) j) + (∑ i, γ i * arch i) := by
  have hs : (∑ i, γ i * Real.log (p : ℝ)) = Real.log (p : ℝ) := by
    rw [← Finset.sum_mul, hγ1, one_mul]
  have h := hviTable_of_collectionLayer γ hγ0 hγ1 n hn D Q (fun _ => Real.log (p : ℝ)) T V arch hV
  simpa [hs] using h

#print axioms badWeighted_collectionBound
#print axioms hviTable_of_collectionLayer
#print axioms hviTable_of_collectionLayer_logp

end LeanFormal.IUT.XiFPaper.Mzk1ULHviTableActual