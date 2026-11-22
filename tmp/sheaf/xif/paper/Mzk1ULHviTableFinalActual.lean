/- U-C Step (viii) (beta) FINAL（Lead 最终裁决：不归一化、聚合字母）。
   两个具名定理:
   * hV_of_collectionLayer: accepted donor weightedAverage_le_collectionBound 的实例化,
     由每个 packet 的 collection ensemble (E, lam, d, oq, iotaL, V, hV) 给出
     每 label 的 collectionBound 上界（字母 D,Q,S=log p,T）;
   * hviTable_final: bad-place 加权聚合（无 Σγ=1）, 聚合字母
     logDK=ΣγD_b, Q=ΣγQ_b, S=Σγ·log p, lstar=ΣγT_b。 -/
import tmp.sheaf.xif.paper.Mzk1ULHviTableActual
import tmp.sheaf.xif.paper.Mzk1URCollectionLayerActual
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Finset
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHviTableFinalActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1ULHviTableActual

/-- 逐 packet 的 Step (v) 字母上界（accepted donor weightedAverage_le_collectionBound
的直接实例化）: collection ensemble 的 λ^Π-加权平均 V 不超过
collectionBound (2n+1) D Q (log p) iotaL, D/Q 为 λ-加权平均的 d·log p / oq·log p。 -/
theorem hV_of_collectionLayer {E : Type*} [Fintype E] [Nonempty E]
    (lam : E → ℝ) (hlam : ∀ e, 0 < lam e)
    (logp : ℝ) (d oq : E → ℝ) (iotaL : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    (V : ∀ j : ℕ, (Fin (j + 1) → E) → ℝ)
    (hV : ∀ j, j ∈ Finset.Icc 1 n → ∀ et : Fin (j + 1) → E,
      V j et ≤ (1 / ((j : ℝ) + 1)) * ∑ idag : Fin (j + 1),
        collectionChoiceBound (2 * (n : ℝ) + 1) logp iotaL j d oq et idag) :
    ∀ j ∈ Finset.Icc 1 n,
      (∑ et : Fin (j + 1) → E, V j et * ∏ k, lam (et k)) /
          (∑ et : Fin (j + 1) → E, ∏ k, lam (et k)) ≤
        collectionBound (2 * (n : ℝ) + 1)
          ((∑ e, d e * logp * lam e) / (∑ e, lam e))
          ((∑ e, oq e * logp * lam e) / (∑ e, lam e))
          logp iotaL j := by
  intro j hj
  have hl : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  exact weightedAverage_le_collectionBound lam hlam (2 * (n : ℝ) + 1) logp
    iotaL hl j d oq (V j) (fun et => hV j hj et)

/-- 会计层（不归一化版，无 Σγ=1 假设）: bad 加权聚合以加权平均字母为界。 -/
theorem hviTable_of_collectionLayer' {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ0 : ∀ i, 0 ≤ γ i)
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

/-- 最终具名 hviTable（Lead 最终裁决: 无 Σγ=1, 聚合字母）。

输入: b = bad-place 指标; γ = nativeBadLocalWeight（仅需非负）; n >= 2; p 固定素数;
D/Q/T : b → ℝ = 每 packet 的 Step(v) 字母（D_b,Q_b,iotaL_b, kurt urColl 口径）;
Vh : b → ℕ → ℝ = 每 packet 每 label 的 λ^Π-加权 hull 平均（由 hV_of_collectionLayer 供）;
hVh = 逐 packet 逐 label 的 collectionBound 比较（arch 记为每 packet 0）。

结论: s3014 := Σ_b γ_b·(1/n)Σ_label Vh_b,label <=
(1/n)Σ_j collectionBound (2n+1) (Σγ D_b) (Σγ Q_b) (Σγ·log p) (Σγ T_b) j。 -/
theorem hviTable_final
    {b : Type*} [Fintype b] (γ : b → ℝ) (hγ0 : ∀ i, 0 ≤ γ i)
    (n : ℕ) (hn : 2 ≤ n)
    (logP : b → ℝ) (D Q T : b → ℝ) (Vh : b → ℕ → ℝ)
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (logP i) (T i) label) :
    (∑ i, γ i * ((1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n, Vh i label))) ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        collectionBound (2 * (n : ℝ) + 1) (∑ i, γ i * D i) (∑ i, γ i * Q i)
          (∑ i, γ i * logP i) (∑ i, γ i * T i) j) := by
  have hVh' : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      Vh i label ≤ collectionBound (2 * (n : ℝ) + 1) (D i) (Q i) (logP i)
        (T i) label + (0 : ℝ) := by
    intro i label hlabel
    simpa using hVh i label hlabel
  have h := hviTable_of_collectionLayer' γ hγ0 (n := n) hn D Q logP T Vh (fun _ => 0) hVh'
  simpa using h

#print axioms hviTable_of_collectionLayer'
#print axioms hV_of_collectionLayer
#print axioms hviTable_final

end LeanFormal.IUT.XiFPaper.Mzk1ULHviTableFinalActual