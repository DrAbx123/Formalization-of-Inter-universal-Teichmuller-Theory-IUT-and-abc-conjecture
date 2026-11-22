/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellXMuPacket
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import Mathlib.Algebra.Module.Submodule.Map

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# IUT-II log-shell 载体层：链的作用/log-volume 相容（R7a/R7b）与逐因子张量腿形（R9）

本文件续 `logs/coordination/vertical-log-kummer-ordered-layer-20261016.md` §21.4 的剩余卡
（R7 作用/log-volume 相容、R8 arch、R9 张量腿形），按依赖序取最小可做者并以缩减 pass
形式闭合：R7a（作用相容，条件形，全部可证）；R7b（log-volume 相容，门 + 复合律）；
R9（逐因子独立腿的最小片段）。R8 与 R6 的评估与精确卡见报告 §23（本文件不形式化 arch）。

## 原文定位（冻结）

* [IUTchIII, Proposition 1.2, (vi)]（`papers/motizuki_corpus/text/Inter-universal
  Teichmuller Theory III.txt` l.1898-1949；非 arch）：`log(†D⊢_v) := {†G_v ↷ k∼(†G_v)}`
  是带连续 `†G_v`-作用的 ind-topological 模；`I†D⊢_v := I(†G_v) ⊆ k∼(†G_v)` 带
  `p_v`-adic log-volume（l.1904-1917）。`†F⊢×μ_v` 数据上的 functorial algorithm 给出
  Ism-轨道 `log(†D⊢_v) ~→ log(†F⊢×μ_v)`（l.1918-1928）；`†F_v` 数据上的 functorial
  algorithm 给出同构链 `log(†D⊢_v) ~→ log(†F⊢×μ_v) ~→ log(†F_v)`（l.1929-1944）。
  末句（l.1944-1949，本文件的冻结句）：「The various isomorphisms of the last two
  displays are compatible with one another, as well as with the respective †G_v- and
  G_v(†Π_v)-actions [relative to the natural identification †G_v = G_v(†Π_v) that arises
  from regarding †D⊢_v as an object constructed from †D_v], the respective log-shells,
  and the respective log-volumes on these log-shells.」四个子句逐条对位：
  「compatible with one another」= 两个 display 共享左腿（卡-D 构造即此）；
  「respective actions」含 l.1946-1948 的标识 = 本文件单一群 `G` 的三侧作用与两条
  等变律（R7a）；「respective log-shells」= 卡-D 像律 + 本文件的作用-稳定性传递；
  「respective log-volumes」= R7b 的门数据与复合律。
* [IUTchIII, Proposition 3.2, (i)]（l.5706-5739）：Q-span 层链 `log(αD⊢_vQ) ~→
  log(αF⊢×μ_vQ) ~→ log(αF_vQ)` 与 A-张量包版本——R7a 的 `*_map_IQSpan` 与 R9 的消费面。
  消费者：Ind2（alien copies 不识别）、Ind3（上半相容）→ Theorem 3.11 → Corollary 3.12
  → ABC；Card-APT、QCMP。
* [IUTchIII, Proposition 1.2, (vii)]（l.1950-1999；arch）：poly-isomorphism = 对
  [AbsTopIII], Proposition 5.8, (v) 构造中各 direct factor 的独立 {±1}-作用的轨道
  （l.1971-1973、l.1982-1984）；A-张量包形状的因子独立性据此。R8 精确卡见报告 §23.4
  （缺 Ψcns 载体与 Ψ×_log-轨道/满射；Hilbert 更正口径）。

## 缩减点（显式标注；不得顶替原命题）

* R7a-1. 原文作用为 ind-topological 模上的连续作用（l.1904-1905）；缩减模型无拓扑，
  以 `K` 的 ℚ-线性自同构承载各侧作用（保存模线性部分，即 Q-span 层消费所需）。
* R7a-2. 三条作用以单一群 `G` 承载（原文 l.1946-1948 的标识 `†G_v = G_v(†Π_v)` 的
  缩减）；Ism-轨道/poly-isomorphism 仍缩为单一 ℚ-线性等价（继承卡-D 缩减点 R6）。
* R7b. `p_v`-adic log-volume 本体（[AbsTopIII], Corollary 5.10, (iv)）未入库：
  log-volume 以 `K → ℝ` 函数为门数据，相容律取 log-shells 上等式；本体的存在性、
  单调性、可加性不在本件内。
* R8. arch 情形不形式化（同卡-D R8）。
* R9. 张量腿取环等价（R2 乘法模型）；本件给出「逐因子独立腿」依赖族最小片段，
  `⊗` 本体不在本件内。

## 与相邻件的区分（只读对照，不 import）

* 卡-D `SourceLogShellXMuChainSupply`（`SourceLogShellXMuPacket.lean:125-130`）：
  本件在其上叠加作用数据（R7a）与 log-volume 数据（R7b），不修改其声明。
* Hilbert 线 `MonoAnalyticLogShellFormalLogMul.lean`（在飞）与本件的关系仅在接口层：
  其 `logOf_mul` 供给 p-进 log 的乘性律（未来 `logMap` 实例化的义务面），本件不 import、
  不重复；见报告 §23.6。
* `VerticalLogKummerCorrespondence`（`IUTII/Kummer/VerticalLogKummer.lean:17`，只读面内）：
  本件 §4 给出其对应级读出成型定理（Leibniz Step(x) 线请求块 2 的片段供给；见报告 §23.8）。
-/

namespace LeanFormal.IUT

/-! ## 1. R7a：链与 †G_v / G_v(†Π_v)-作用的相容（条件形，[IUTchIII, Prop 1.2, (vi), l.1944-1949]） -/

/-- 三向链的作用相容供给（R7a，条件形）。

按 [IUTchIII, Proposition 1.2, (vi) 末句]（l.1944-1949）列出「respective †G_v- and
G_v(†Π_v)-actions」的缩减供给物：三侧作用

* `sourceAction i`：`†G_v` 在 `log(†D⊢_v)`（载体 `(D i).K`）上的作用
  （原文 l.1904-1912 的「continuous †G_v-action」）；
* `middleAction i`：`G_v(†Π_v)` 在 `log(†F⊢×μ_v)`（载体 `(X i).K`）上的作用；
* `targetAction i`：`G_v(†Π_v)` 在 `log(†F_v)`（载体 `(F i).K`）上的作用；

以及两条等变律 `left_equivariant` / `right_equivariant`（「compatible with the
respective actions」的逐腿读出）。缩减：单一群 `G`（原文 l.1946-1948 的标识
`†G_v = G_v(†Π_v)`，缩减点 R7a-2）；作用为 ℚ-线性自同构（R7a-1）。 -/
structure SourceLogShellXMuChainActionCompatibility {ι : Type*}
    (D X F : ι → SourceLogShellDatum) (G : Type*) [Group G]
    (S : SourceLogShellXMuChainSupply D X F) where
  sourceAction : (i : ι) → G →* ((D i).K ≃ₗ[ℚ] (D i).K)
  middleAction : (i : ι) → G →* ((X i).K ≃ₗ[ℚ] (X i).K)
  targetAction : (i : ι) → G →* ((F i).K ≃ₗ[ℚ] (F i).K)
  left_equivariant : ∀ (i : ι) (g : G) (x : (D i).K),
    S.leftEquiv i (sourceAction i g x) = middleAction i g (S.leftEquiv i x)
  right_equivariant : ∀ (i : ι) (g : G) (x : (X i).K),
    S.rightEquiv i (middleAction i g x) = targetAction i g (S.rightEquiv i x)

namespace SourceLogShellXMuChainActionCompatibility

variable {ι : Type*} {D X F : ι → SourceLogShellDatum} {G : Type*} [Group G]
  {S : SourceLogShellXMuChainSupply D X F}

/-- 复合腿与作用相容（「compatible ... with the respective actions」的复合腿读出）：
`chainEquiv (σ • x) = σ • (chainEquiv x)`。 -/
theorem chainEquiv_equivariant (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (g : G) (x : (D i).K) :
    S.chainEquiv i (A.sourceAction i g x) = A.targetAction i g (S.chainEquiv i x) := by
  simp only [SourceLogShellXMuChainSupply.chainEquiv, LinearEquiv.trans_apply]
  rw [A.left_equivariant i g x, A.right_equivariant i g (S.leftEquiv i x)]

/-- 轨道形式：链腿把 `x` 的 `G`-轨道送到 `chainEquiv x` 的 `G`-轨道
（原文 l.1921-1928「Ism-orbit」在单一等价下的轨道像律；缩减点 R7a-2）。 -/
theorem chainEquiv_image_orbit (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (x : (D i).K) :
    S.chainEquiv i '' { y : (D i).K | ∃ g : G, A.sourceAction i g x = y } =
      { y : (F i).K | ∃ g : G, A.targetAction i g (S.chainEquiv i x) = y } := by
  ext y
  constructor
  · rintro ⟨z, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, (A.chainEquiv_equivariant i g x).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨A.sourceAction i g x, ⟨g, rfl⟩, A.chainEquiv_equivariant i g x⟩

/-- 作用与 log-shell 的相容传递（中间侧）：若源侧作用保持 `I†D⊢_v`，则中间侧作用
保持 `I†F⊢×μ_v`（由左腿像律 + 等变律；原文 l.1944-1949 的「respective log-shells」
与作用子句的交互）。 -/
theorem middleAction_preserves_logShell (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (g : G) (hsrc : A.sourceAction i g '' (D i).logShell = (D i).logShell) :
    A.middleAction i g '' (X i).logShell = (X i).logShell := by
  calc A.middleAction i g '' (X i).logShell
      = A.middleAction i g '' (S.leftEquiv i '' (D i).logShell) := by
          rw [S.leftEquiv_image_logShell i]
    _ = (fun x : (D i).K => A.middleAction i g (S.leftEquiv i x)) '' (D i).logShell :=
          Set.image_image (⇑(A.middleAction i g)) (⇑(S.leftEquiv i)) (D i).logShell
    _ = (fun x : (D i).K => S.leftEquiv i (A.sourceAction i g x)) '' (D i).logShell := by
          exact congrArg (fun f : (D i).K → (X i).K => f '' (D i).logShell)
            (funext (fun x => (A.left_equivariant i g x).symm))
    _ = S.leftEquiv i '' (A.sourceAction i g '' (D i).logShell) :=
          (Set.image_image (⇑(S.leftEquiv i)) (⇑(A.sourceAction i g)) (D i).logShell).symm
    _ = S.leftEquiv i '' (D i).logShell := by rw [hsrc]
    _ = (X i).logShell := S.leftEquiv_image_logShell i

/-- 作用与 log-shell 的相容传递（目标侧，经复合腿）：若源侧作用保持 `I†D⊢_v`，
则目标侧作用保持 `I†F_v`。 -/
theorem targetAction_preserves_logShell (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (g : G) (hsrc : A.sourceAction i g '' (D i).logShell = (D i).logShell) :
    A.targetAction i g '' (F i).logShell = (F i).logShell := by
  calc A.targetAction i g '' (F i).logShell
      = A.targetAction i g '' (S.chainEquiv i '' (D i).logShell) := by
          rw [S.chainEquiv_image_logShell i]
    _ = (fun x : (D i).K => A.targetAction i g (S.chainEquiv i x)) '' (D i).logShell :=
          Set.image_image (⇑(A.targetAction i g)) (⇑(S.chainEquiv i)) (D i).logShell
    _ = (fun x : (D i).K => S.chainEquiv i (A.sourceAction i g x)) '' (D i).logShell := by
          exact congrArg (fun f : (D i).K → (F i).K => f '' (D i).logShell)
            (funext (fun x => (A.chainEquiv_equivariant i g x).symm))
    _ = S.chainEquiv i '' (A.sourceAction i g '' (D i).logShell) :=
          (Set.image_image (⇑(S.chainEquiv i)) (⇑(A.sourceAction i g)) (D i).logShell).symm
    _ = S.chainEquiv i '' (D i).logShell := by rw [hsrc]
    _ = (F i).logShell := S.chainEquiv_image_logShell i

/-- Q-span 层作用稳定性（源侧；[IUTchIII, Prop 3.2, (i)] 的 Q-span 读数）：
若源侧作用保持 log-shell，则它保持 `IQ(αD⊢_vQ)`。 -/
theorem sourceAction_map_IQSpan (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (g : G) (hsrc : A.sourceAction i g '' (D i).logShell = (D i).logShell) :
    Submodule.map (A.sourceAction i g).toLinearMap (D i).IQSpan = (D i).IQSpan := by
  simp only [SourceLogShellDatum.IQSpan]
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap, hsrc]

/-- Q-span 层作用稳定性（中间侧，经传递引理）。 -/
theorem middleAction_map_IQSpan (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (g : G) (hsrc : A.sourceAction i g '' (D i).logShell = (D i).logShell) :
    Submodule.map (A.middleAction i g).toLinearMap (X i).IQSpan = (X i).IQSpan := by
  simp only [SourceLogShellDatum.IQSpan]
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap,
    A.middleAction_preserves_logShell i g hsrc]

/-- Q-span 层作用稳定性（目标侧，经复合腿传递引理）。 -/
theorem targetAction_map_IQSpan (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (i : ι) (g : G) (hsrc : A.sourceAction i g '' (D i).logShell = (D i).logShell) :
    Submodule.map (A.targetAction i g).toLinearMap (F i).IQSpan = (F i).IQSpan := by
  simp only [SourceLogShellDatum.IQSpan]
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap,
    A.targetAction_preserves_logShell i g hsrc]

/-- vQ 包层作用等变（逐点形式）：复合腿在包层与作用交换
（`piCongrRight chain (σ • x) = σ • (piCongrRight chain x)`）。 -/
theorem packet_equivariant (A : SourceLogShellXMuChainActionCompatibility D X F G S)
    (g : G) (x : (i : ι) → (D i).K) :
    LinearEquiv.piCongrRight S.chainEquiv (fun i => A.sourceAction i g (x i)) =
      fun i => A.targetAction i g (LinearEquiv.piCongrRight S.chainEquiv x i) := by
  funext i
  rw [LinearEquiv.piCongrRight_apply, LinearEquiv.piCongrRight_apply]
  exact A.chainEquiv_equivariant i g (x i)

end SourceLogShellXMuChainActionCompatibility

/-! ## 2. R7b：链与 log-volume 的相容（门 + 复合律；[IUTchIII, Prop 1.2, (vi), l.1948-1949]） -/

/-- 三向链的 log-volume 相容供给（R7b，条件形）。原文（l.1948-1949）：
「compatible ... with ... the respective log-volumes on these log-shells」——
三侧 log-volume 以函数 `K → ℝ` 为门数据（`p_v`-adic log-volume 本体未入库，缩减点 R7b；
有限值对应原文 l.1875-1876 的「compact, hence of finite log-volume」，l.1917 的
`p_v`-adic log-volume），相容律为 log-shells 上的等式。 -/
structure SourceLogShellXMuChainLogVolumeCompatibility {ι : Type*}
    (D X F : ι → SourceLogShellDatum) (S : SourceLogShellXMuChainSupply D X F) where
  sourceVolume : (i : ι) → (D i).K → ℝ
  middleVolume : (i : ι) → (X i).K → ℝ
  targetVolume : (i : ι) → (F i).K → ℝ
  left_compatible : ∀ (i : ι) (x : (D i).K), x ∈ (D i).logShell →
    middleVolume i (S.leftEquiv i x) = sourceVolume i x
  right_compatible : ∀ (i : ι) (x : (X i).K), x ∈ (X i).logShell →
    targetVolume i (S.rightEquiv i x) = middleVolume i x

namespace SourceLogShellXMuChainLogVolumeCompatibility

variable {ι : Type*} {D X F : ι → SourceLogShellDatum}
  {S : SourceLogShellXMuChainSupply D X F}

/-- 复合腿的 log-volume 相容（两条单腿律经中间包的复合；原文「compatible with ...
the respective log-volumes」的复合读出）。 -/
theorem chain_compatible (V : SourceLogShellXMuChainLogVolumeCompatibility D X F S)
    (i : ι) (x : (D i).K) (hx : x ∈ (D i).logShell) :
    V.targetVolume i (S.chainEquiv i x) = V.sourceVolume i x := by
  have hmem : S.leftEquiv i x ∈ (X i).logShell := by
    rw [← S.leftEquiv_image_logShell i]
    exact ⟨x, hx, rfl⟩
  simp only [SourceLogShellXMuChainSupply.chainEquiv, LinearEquiv.trans_apply]
  rw [V.right_compatible i (S.leftEquiv i x) hmem, V.left_compatible i x hx]

/-- log-volume 上界的链上传递（消费者形状：Cor 3.12 的 log-volume 上界、QCMP 的
Q-span/log-volume 比较）：若目标侧 log-shell 上 `targetVolume ≤ h`，则源侧 log-shell 上
`sourceVolume ≤ h`。 -/
theorem chainVolume_le_of_targetBound (V : SourceLogShellXMuChainLogVolumeCompatibility D X F S)
    (i : ι) {h : ℝ}
    (hbound : ∀ y : (F i).K, y ∈ (F i).logShell → V.targetVolume i y ≤ h)
    {x : (D i).K} (hx : x ∈ (D i).logShell) :
    V.sourceVolume i x ≤ h := by
  have hmem : S.chainEquiv i x ∈ (F i).logShell := by
    rw [← S.chainEquiv_image_logShell i]
    exact ⟨x, hx, rfl⟩
  calc V.sourceVolume i x = V.targetVolume i (S.chainEquiv i x) :=
        (V.chain_compatible i x hx).symm
    _ ≤ h := hbound _ hmem

end SourceLogShellXMuChainLogVolumeCompatibility

/-! ## 3. R9：逐因子独立张量腿（最小片段；[IUTchIII, Prop 1.2, (vi)/(vii)] 的 A-张量包形状） -/

/-- 逐因子独立腿的依赖族张量包集（缩减点 R9：张量因子 `α` 的载体 `K α` 与集合 `t α`
逐因子独立，无跨因子耦合；原文 A-张量包 `log(AD⊢_vQ) = ⊗_α log(αD⊢_vQ)` 的因子独立性
形状——[IUTchIII, Prop 3.2, (i), l.5718-5730] 的 A-包版本）。 -/
def sourceLogShellDependentTensorSet {A : Type*} (K : A → Type*) (t : ∀ α, Set (K α)) :
    Set ((α : A) → K α) :=
  {x | ∀ α, x α ∈ t α}

/-- 逐因子腿族的像律（R9 最小片段）：`e '' piSet t = piSet (fun α => e α '' t α)`——
腿族 `e` 逐因子独立作用，无跨因子耦合。逆方向对每因子用选择取原像后组合
（`Classical.choice`）。 -/
theorem sourceLogShellDependentTensorSet_image_map {A : Type*} {K K' : A → Type*}
    (e : ∀ α, K α → K' α) (t : ∀ α, Set (K α)) :
    (fun x : (α : A) → K α => fun α => e α (x α)) ''
      sourceLogShellDependentTensorSet K t =
    sourceLogShellDependentTensorSet K' (fun α => e α '' t α) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact fun α => ⟨x α, hx α, rfl⟩
  · intro hz
    refine ⟨fun α => Classical.choose (hz α),
      fun α => (Classical.choose_spec (hz α)).1, ?_⟩
    funext α
    exact (Classical.choose_spec (hz α)).2

/-- 逐因子独立腿的链供给（R9 最小片段的结构形）：每因子 `α` 各自一对环等价腿
`leftEquiv α`、`rightEquiv α`（独立于其它因子；原文 functorial algorithm 逐因子并置）。 -/
structure SourceLogShellDependentTensorChainSupply {A : Type*} (K K' K'' : A → Type*)
    [∀ α, Field (K α)] [∀ α, CharZero (K α)]
    [∀ α, Field (K' α)] [∀ α, CharZero (K' α)]
    [∀ α, Field (K'' α)] [∀ α, CharZero (K'' α)] where
  leftEquiv : ∀ α, K α ≃+* K' α
  rightEquiv : ∀ α, K' α ≃+* K'' α

namespace SourceLogShellDependentTensorChainSupply

variable {A : Type*} {K K' K'' : A → Type*}
  [∀ α, Field (K α)] [∀ α, CharZero (K α)]
  [∀ α, Field (K' α)] [∀ α, CharZero (K' α)]
  [∀ α, Field (K'' α)] [∀ α, CharZero (K'' α)]

/-- 逐因子复合腿（先左腿再右腿，逐因子）。 -/
def chainEquiv (T : SourceLogShellDependentTensorChainSupply K K' K'') (α : A) :
    K α ≃+* K'' α :=
  (T.leftEquiv α).trans (T.rightEquiv α)

/-- 左腿族像律。 -/
theorem left_image (T : SourceLogShellDependentTensorChainSupply K K' K'')
    (t : ∀ α, Set (K α)) :
    (fun x : (α : A) → K α => fun α => T.leftEquiv α (x α)) ''
      sourceLogShellDependentTensorSet K t =
    sourceLogShellDependentTensorSet K' (fun α => T.leftEquiv α '' t α) :=
  sourceLogShellDependentTensorSet_image_map (fun α => T.leftEquiv α) t

/-- 右腿族像律。 -/
theorem right_image (T : SourceLogShellDependentTensorChainSupply K K' K'')
    (t : ∀ α, Set (K' α)) :
    (fun x : (α : A) → K' α => fun α => T.rightEquiv α (x α)) ''
      sourceLogShellDependentTensorSet K' t =
    sourceLogShellDependentTensorSet K'' (fun α => T.rightEquiv α '' t α) :=
  sourceLogShellDependentTensorSet_image_map (fun α => T.rightEquiv α) t

/-- 复合腿族像律（链式复合的逐因子形；R9 最小片段）。 -/
theorem chain_image (T : SourceLogShellDependentTensorChainSupply K K' K'')
    (t : ∀ α, Set (K α)) :
    (fun x : (α : A) → K α => fun α => T.chainEquiv α (x α)) ''
      sourceLogShellDependentTensorSet K t =
    sourceLogShellDependentTensorSet K'' (fun α => T.chainEquiv α '' t α) :=
  sourceLogShellDependentTensorSet_image_map (fun α => T.chainEquiv α) t

end SourceLogShellDependentTensorChainSupply

/-! ## 4. 载体→ `VerticalLogKummerCorrespondence` 的读出成型（Leibniz Step(x) 线请求块 2 的片段供给） -/

/-- 载体→对应合约的读出成型（`hullDominates_of_sourceLogShell` 的
`VerticalLogKummerCorrespondence` 级版本；root 转递 Leibniz Step(x) 线请求块 2：
命名载体接口把构造核的 Ind3-lift 与 log-shell 坐标侧衔接）。给定核侧读出
`φ : ∀ m, L.F m → D.Units`（经 `logMap` 给出 kummer 读出）、`measure : D.K → L.D`
（log 坐标 → 有序值读出）的因子化律 `hfactor`（kummer/log-volume 读出相容）与
`measure` 在 log-shell 上的界，则 `HullDominates`（粗空间值律上升为源读出的形状）。
证明只用 `codomainKummerContained`、`hfactor`、`hmeasure`，不用有序层律
（无需 `VerticalLogKummerOrderedLayer` 的单调性字段；有序层版本见
`SourceLogShellCarrier.lean:332`）。消费者：Cor 3.12 Step (x)/(xi)、Card-APT。 -/
theorem VerticalLogKummerCorrespondence.hullDominates_of_sourceLogShell {D : SourceLogShellDatum}
    (h : D.codomainKummerContained) (L : VerticalLogKummerCorrespondence)
    (φ : ∀ m : ℕ, L.F m → D.Units) (measure : D.K → L.D)
    (hfactor : ∀ (m : ℕ) (x : L.F m),
      L.kummer m x = measure ((D.logMap (φ m x)).toAdd))
    {hull : L.D} (hmeasure : ∀ a ∈ D.logShell, measure a ≤ hull) (x₀ : L.F 0) :
    L.HullDominates x₀ hull := by
  intro n
  rw [hfactor]
  exact hmeasure _ (h ⟨φ (0 + n) (L.transport 0 n x₀), rfl⟩)

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：链的作用/log-volume 相容（R7a/R7b）与逐因子张量腿形（R9 最小片段）；
义务 `IUT-II.vertical-log-kummer` 的剩余卡 R7 下钻件（条件形）。 -/
def sourceLogShellActionCompatibility : Obligation :=
  { id := "IUT-II.source-log-shell-action-compatibility"
    source := "IUT III, Proposition 1.2, (vi) final sentence (text l.1944-1949); " ++
      "Proposition 3.2, (i) (l.5706-5739); (vii) l.1950-1999"
    status := VerificationStatus.conditional
    note :=
      "Action/log-volume compatibility of the three-way chain (Proposition 1.2, (vi) " ++
        "final sentence) and the per-factor tensor-leg shape (R9 minimal fragment), " ++
        "reduced pass. Proved conditional on the card-D chain gate: composite-leg " ++
        "equivariance for the respective actions, orbit image law, transfer of " ++
        "log-shell stability from source to middle/target, Q-span action stability, " ++
        "packet-level pointwise equivariance, log-volume composite compatibility and " ++
        "log-volume bound transfer, and the per-factor independent dependent-tensor " ++
        "leg image law with its chain composite. Reductions (labeled): R7a-1 actions " ++
        "as Q-linear automorphisms (no topology); R7a-2 single group G (source " ++
        "identification dagger-G-v = G-v(dagger-Pi-v)), Ism-orbits collapsed to " ++
        "single Q-linear equivalences (inherited R6); R7b the p-adic log-volume " ++
        "itself is gate data with real values (no source layer); R8 arch not " ++
        "formalized (precise card in the report); R9 ring-equivalence legs " ++
        "(multiplicative model R2), the tensor product proper not formalized. " ++
        "Additionally supplies the correspondence-level readout assembly " ++
        "VerticalLogKummerCorrespondence.hullDominates_of_sourceLogShell " ++
        "(fragment supply for the Leibniz Step-x request block 2)."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-xmu-packet" ] }

end LeanFormal.IUT.Audit
