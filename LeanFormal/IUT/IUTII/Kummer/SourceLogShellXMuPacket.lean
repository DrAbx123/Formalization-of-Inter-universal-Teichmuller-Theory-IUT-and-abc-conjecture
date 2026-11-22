/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import Mathlib.Algebra.Module.Submodule.Map

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# IUT-II log-shell 载体层：×μ 中间包与三向 poly-iso 链（卡-D，缩减 pass）

本文件下钻卡-C 的剩余卡 3（`logs/coordination/vertical-log-kummer-ordered-layer-20261016.md`
§14/§20）：「`log(†D⊢_v) ~→ log(†F⊢×μ_v) ~→ log(†F_v)` 三向链的中间包 `log(†F⊢×μ_v)`
载体/接口与链式复合」。消费者：Ind2（alien copies 不识别）、Ind3（上半相容）→
Theorem 3.11 → Corollary 3.12 → ABC；并供 Card-APT / QCMP 的 Q-span 层读数。

## 原文定位（冻结）

* [IUTchIII, Proposition 1.2, (vi)]（`papers/motizuki_corpus/text/Inter-universal Teichmuller
  Theory III.txt`，l.1900-1949；非 arch）：functorial algorithm in †F⊢×μ_v 数据构造
  Ism-orbit of isomorphisms `log(†D⊢_v) ~→ log(†F⊢×μ_v)`（l.1918-1928）；functorial
  algorithm in †F_v 数据构造同构链 `log(†D⊢_v) ~→ log(†F⊢×μ_v) ~→ log(†F_v)`
  （l.1929-1944）；「compatible ... with the respective log-shells」（l.1944-1949）。
* [IUTchIII, Proposition 1.2, (vii)]（l.1950-1999；arch）：对应 poly-isomorphism 版
  （独立 {±1} 作用的轨道）。
* [IUTchIII, Proposition 3.2, (i)]（l.5706-5739）：「Mono-analytic/Holomorphic
  Compatibility」：上述 poly-isomorphisms 诱导 ind-topological modules 的自然
  poly-isomorphisms `log(αD⊢_vQ) ~→ log(αF⊢×μ_vQ) ~→ log(αF_vQ)`（l.5718-5724）、
  `log(AD⊢_vQ) ~→ log(AF⊢×μ_vQ) ~→ log(AF_vQ)`（l.5724-5730）与混合包（l.5731-5737）；
  中间项即 `log(†F⊢×μ_v)` 及其包版本。
* 原文证明（l.5786-5787）：「follow immediately from the definitions and the references
  quoted」——诱导 poly-isomorphism 是 ⊕/⊗ 函子性的直接推论；本文件把该函子性实现为
  （左、右）腿的像律及其复合。

## 本文件的命题（冻结形状；缩减形式）

1. 中间包载体（vQ 层）：`sourceLogShellXMuPacket X = IQ(αF⊢×μ_vQ)`，连同分解律
   `= span(∏_v logShell(F⊢×μ)_v)`、成员刻画、直和项含入（原文 l.5701-5705 的
   「by replacing "D⊢" ... by "F⊢×μ"」）。
2. 三向链供给（source gate）：`SourceLogShellXMuChainSupply D X F`：左腿
   `log(†D⊢_v) → log(†F⊢×μ_v)`、右腿 `log(†F⊢×μ_v) → log(†F_v)`（各为单一 ℚ-线性等价，
   缩减点 R6），两条与 log-shell 的像相容律（原文 l.1944-1949 的读出，缩减点 R3）。
3. 链复合（条件形）：复合腿 `chainEquiv`；纤维级 log-shell/IQSpan 像律；vQ 包层
   `map (piCongrRight 复合腿) IQ(αD⊢_vQ) = IQ(αF_vQ)`——经中间包的两次卡-C 像律组装
   （原文 l.5718-5724 第一 display）；直和项 `Pi.single` 的逐点兼容（l.5692）。
4. 张量层链（条件形，R2 乘法模型）：`sourceLogShell_tensorChain_image_comp`：先左腿后右腿
   的张量包像 = 复合腿的像（原文 l.5724-5730 第二 display 的缩减形；中段即
   `log(AF⊢×μ_vQ)` 的缩减载体）。

## 缩减点（显式标注；不得顶替原命题）

R1-R5 同卡-C（有限直和=依赖函数空间；⊗ 经乘法像；poly-isomorphism→单一等价；arch 不
形式化；混合包 `log(A,αD⊢_v)` 未形式化）。
R6. 链腿的 functorial algorithm 内容不形式化：Ism-orbit / poly-isomorphism 缩为单一
    ℚ-线性等价；中间数据族 `X` 的载体（`K`、`logShell`）即底层 F⊢×μ-数据层未入库时的
    接口请求（按原文列供给物：†F⊢×μ_v 的数据、†F_v 的数据、各腿的存在性与 log-shell 相容性）。
R7. [IUTchIII, Proposition 1.2, (vi) 末句] 的 †G_v / G_v(†Π_v)-作用相容与 log-volume 相容
    不形式化（log-volume 线对象在别处）。
R8. (vii) 的 arch 情形（Hermitian 闭单位球、{±1}-轨道）不形式化（同 R4）。
R9. 张量层链腿取环等价（R2 乘法模型的代价：把因子级模同构缩为交换乘积的单一乘性腿）；
    fibre 层腿仍是 ℚ-线性等价，两层供给独立列明。

## 与相邻对象的区分（只读对照，不 import）

* F-prime-strip 层 ×μ 载体 `SourceFTimesMuPrimeStrip`（`IUTIII/Theorem311/
  SourceFTimesMuPrimeStripPolyIsomorphism.lean`）是核=有限阶元的商/作用载体；本文件
  中间包是 log-shell 的 Q-span 子模（`Submodule ℚ`）。两层经「中间包供给」对接——
  type-level bridge 未完成，作为接口请求记录在报告。
* `IUTII/Kummer/TimesMuQuotient.lean` 的 `quotientMap`（商接口）是同一仓库的既有件，
  本文件不 import；未来可由其纤维构造中间包供给。
-/

open scoped Pointwise

namespace LeanFormal.IUT

/-! ## 1. F⊢×μ 中间包（vQ 层载体） -/

/-- `IQ(αF⊢×μ_vQ)`：F⊢×μ-版 1-tensor 包的 `Q`-span（三向链的中间包）。

原文 [IUTchIII, Proposition 3.2, l.5701-5705]（「we shall use similar notation ...
by replacing "D⊢" in the above notational conventions by "F⊢×μ"」）与 l.5721-5722 的
中间项 `log(αF⊢×μ_vQ)`。定义即卡-C 一般直和包 `sourceLogShellIQDirectSumPacket`
在中间数据族 `X`（各纤维为 `log(†F⊢×μ_v)` 的缩减载体）上的求值。 -/
def sourceLogShellXMuPacket {ι : Type*} (X : ι → SourceLogShellDatum) :
    Submodule ℚ ((i : ι) → (X i).K) :=
  sourceLogShellIQDirectSumPacket X

/-- 中间包分解律：`IQ(⨁_{v|vQ} I(†F⊢×μ_v)) = span (∏_{v|vQ} I(†F⊢×μ_v))`
（卡-C `sourceLogShellIQDirectSumPacket_eq_span_pi` 的中间包命名版）。 -/
theorem sourceLogShellXMuPacket_eq_span_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → SourceLogShellDatum) :
    sourceLogShellXMuPacket X = Submodule.span ℚ (sourceLogShellDirectSumPacketSet X) :=
  sourceLogShellIQDirectSumPacket_eq_span_pi X

/-- 中间包成员逐纤维刻画：`x ∈ IQ(αF⊢×μ_vQ) ↔ ∀ v, x_v ∈ IQ(I(†F⊢×μ_v))`。 -/
theorem sourceLogShellXMuPacket_mem_iff {ι : Type*} (X : ι → SourceLogShellDatum)
    (x : (i : ι) → (X i).K) :
    x ∈ sourceLogShellXMuPacket X ↔ ∀ i, x i ∈ (X i).IQSpan :=
  sourceLogShellIQDirectSumPacket_mem_iff X x

/-- 中间包的直和项含入（原文 l.5692「the direct summand with subscript v」的中间包版）。 -/
theorem sourceLogShellXMuPacket_single_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → SourceLogShellDatum) (i : ι) {x : (X i).K} (hx : x ∈ (X i).IQSpan) :
    (LinearMap.single ℚ (fun i => (X i).K) i x) ∈ sourceLogShellXMuPacket X :=
  sourceLogShellIQDirectSumPacket_single_mem X i hx

/-! ## 2. 三向链供给（source gate） -/

/-- 三向链 `log(†D⊢_v) ~→ log(†F⊢×μ_v) ~→ log(†F_v)` 的 source gate（缩减形）。

按 [IUTchIII, Proposition 1.2, (vi)]（l.1900-1949；非 arch）、(vii)（l.1950-1999；arch）
列出供给物：
* `leftEquiv i : (D i).K ≃ₗ[ℚ] (X i).K`：左腿 `log(†D⊢_v) ~→ log(†F⊢×μ_v)`
  （原文 l.1918-1928「an Ism-orbit of isomorphisms」；缩减点 R6：轨道 → 单一等价）；
* `rightEquiv i : (X i).K ≃ₗ[ℚ] (F i).K`：右腿 `log(†F⊢×μ_v) ~→ log(†F_v)`
  （原文 l.1929-1944 的第二段）；
* 两条 `*_image_logShell`：与各自 log-shell 的相容性（原文 l.1944-1949 一句的
  Q-span 层读出，缩减点 R3）：把 mono-analytic log-shell 送到 mono-analytic log-shell。
其中 `X i`（其 `K` 与 `logShell`）即 `log(†F⊢×μ_v)` 与 `I†F⊢×μ_v` 的缩减载体；
`D`、`F` 分别为 `log(†D⊢_v)`、`log(†F_v)` 的冻结载体（`SourceLogShellDatum`）。
未形式化项见 R7（作用/log-volume 相容）、R8（arch）。 -/
structure SourceLogShellXMuChainSupply {ι : Type*}
    (D X F : ι → SourceLogShellDatum) where
  leftEquiv : (i : ι) → (D i).K ≃ₗ[ℚ] (X i).K
  rightEquiv : (i : ι) → (X i).K ≃ₗ[ℚ] (F i).K
  leftEquiv_image_logShell : ∀ i, leftEquiv i '' (D i).logShell = (X i).logShell
  rightEquiv_image_logShell : ∀ i, rightEquiv i '' (X i).logShell = (F i).logShell

namespace SourceLogShellXMuChainSupply

variable {ι : Type*} {D X F : ι → SourceLogShellDatum}

/-- 链的复合腿 `log(†D⊢_v) ~→ log(†F_v)`（原文两段 display 的复合，经中间对象）。 -/
def chainEquiv (S : SourceLogShellXMuChainSupply D X F) (i : ι) :
    (D i).K ≃ₗ[ℚ] (F i).K :=
  (S.leftEquiv i).trans (S.rightEquiv i)

/-- 复合腿与 log-shell 相容（两条 gate 相容律的复合；原文 l.1944-1949）。 -/
theorem chainEquiv_image_logShell (S : SourceLogShellXMuChainSupply D X F) (i : ι) :
    S.chainEquiv i '' (D i).logShell = (F i).logShell := by
  have hcomp : ⇑(S.chainEquiv i) = ⇑(S.rightEquiv i) ∘ ⇑(S.leftEquiv i) := by
    funext x
    simp only [SourceLogShellXMuChainSupply.chainEquiv, LinearEquiv.trans_apply,
      Function.comp_apply]
  calc S.chainEquiv i '' (D i).logShell
      = (⇑(S.rightEquiv i) ∘ ⇑(S.leftEquiv i)) '' (D i).logShell := by rw [hcomp]
    _ = ⇑(S.rightEquiv i) '' (⇑(S.leftEquiv i) '' (D i).logShell) :=
        (Set.image_image ⇑(S.rightEquiv i) ⇑(S.leftEquiv i) (D i).logShell).symm
    _ = ⇑(S.rightEquiv i) '' (X i).logShell := by rw [S.leftEquiv_image_logShell i]
    _ = (F i).logShell := S.rightEquiv_image_logShell i

/-- 左腿把 D⊢-侧 `I` 的 `Q`-span 送到中间包的 `Q`-span（原文 Proposition 3.2, (ii)
「integral structures on the Q-spans」的链腿读数）。 -/
theorem leftEquiv_map_IQSpan (S : SourceLogShellXMuChainSupply D X F) (i : ι) :
    Submodule.map (S.leftEquiv i).toLinearMap (D i).IQSpan = (X i).IQSpan := by
  simp only [SourceLogShellDatum.IQSpan]
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap, S.leftEquiv_image_logShell i]

/-- 右腿把中间包的 `Q`-span 送到 F-侧的 `Q`-span。 -/
theorem rightEquiv_map_IQSpan (S : SourceLogShellXMuChainSupply D X F) (i : ι) :
    Submodule.map (S.rightEquiv i).toLinearMap (X i).IQSpan = (F i).IQSpan := by
  simp only [SourceLogShellDatum.IQSpan]
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap, S.rightEquiv_image_logShell i]

/-- 复合腿把 D⊢-侧 `Q`-span 送到 F-侧 `Q`-span。 -/
theorem chainEquiv_map_IQSpan (S : SourceLogShellXMuChainSupply D X F) (i : ι) :
    Submodule.map (S.chainEquiv i).toLinearMap (D i).IQSpan = (F i).IQSpan := by
  simp only [SourceLogShellDatum.IQSpan]
  rw [Submodule.map_span, LinearEquiv.coe_toLinearMap, S.chainEquiv_image_logShell i]

/-- 左腿在 vQ 包层的像律（经卡-C 像律消费 gate 相容律）：
`map (piCongrRight leftEquiv) IQ(αD⊢_vQ) = IQ(αF⊢×μ_vQ)`。 -/
theorem left_packet_map (S : SourceLogShellXMuChainSupply D X F) [Fintype ι] [DecidableEq ι] :
    Submodule.map (LinearEquiv.piCongrRight S.leftEquiv).toLinearMap
      (sourceLogShellIQDirectSumPacket D) = sourceLogShellXMuPacket X :=
  sourceLogShellIQDirectSumPacket_map_of_image D X S.leftEquiv S.leftEquiv_image_logShell

/-- 右腿在 vQ 包层的像律：`map (piCongrRight rightEquiv) IQ(αF⊢×μ_vQ) = IQ(αF_vQ)`。 -/
theorem right_packet_map (S : SourceLogShellXMuChainSupply D X F) [Fintype ι] [DecidableEq ι] :
    Submodule.map (LinearEquiv.piCongrRight S.rightEquiv).toLinearMap
      (sourceLogShellXMuPacket X) = sourceLogShellIQDirectSumPacket F :=
  sourceLogShellIQDirectSumPacket_map_of_image X F S.rightEquiv S.rightEquiv_image_logShell

/-- 三向链在 vQ 包层的复合像律（原文 l.5718-5724 第一 display）：
`map (piCongrRight (right ∘ left)) IQ(αD⊢_vQ) = IQ(αF_vQ)`；
由两条单腿像律（中间包 `IQ(αF⊢×μ_vQ)` 显式出现）复合组装。 -/
theorem packet_map (S : SourceLogShellXMuChainSupply D X F) [Fintype ι] [DecidableEq ι] :
    Submodule.map (LinearEquiv.piCongrRight S.chainEquiv).toLinearMap
      (sourceLogShellIQDirectSumPacket D) = sourceLogShellIQDirectSumPacket F := by
  have hcomp : (LinearEquiv.piCongrRight S.chainEquiv).toLinearMap =
      (LinearEquiv.piCongrRight S.rightEquiv).toLinearMap.comp
        (LinearEquiv.piCongrRight S.leftEquiv).toLinearMap := by
    ext x i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.piCongrRight_apply, SourceLogShellXMuChainSupply.chainEquiv,
      LinearEquiv.trans_apply]
  have hmap : Submodule.map ((LinearEquiv.piCongrRight S.rightEquiv).toLinearMap.comp
        (LinearEquiv.piCongrRight S.leftEquiv).toLinearMap)
        (sourceLogShellIQDirectSumPacket D)
      = Submodule.map (LinearEquiv.piCongrRight S.rightEquiv).toLinearMap
          (Submodule.map (LinearEquiv.piCongrRight S.leftEquiv).toLinearMap
            (sourceLogShellIQDirectSumPacket D)) :=
    Submodule.map_comp _ _ _
  rw [hcomp, hmap, S.left_packet_map, S.right_packet_map]

/-- 包层链把「subscript v 的直和项」送到对应直和项（原文 l.5692）。 -/
theorem packet_apply_single (S : SourceLogShellXMuChainSupply D X F) [DecidableEq ι]
    (i : ι) (x : (D i).K) :
    LinearEquiv.piCongrRight S.chainEquiv (Pi.single i x) =
      Pi.single i (S.chainEquiv i x) := by
  ext j
  rw [LinearEquiv.piCongrRight_apply]
  exact Pi.apply_single (fun i => ⇑(S.chainEquiv i)) (fun i => by simp) i x j

end SourceLogShellXMuChainSupply

/-! ## 3. 张量（n-tensor）层链（R2 乘法模型；原文 l.5724-5730 第二 display） -/

/-- 张量包链式复合（缩减形）：先左腿 `eL` 再右腿 `eR` 的张量包像等于复合腿
`eL.trans eR` 的像。中段对象即 `log(AF⊢×μ_vQ)` 的缩减载体
`sourceLogShellTensorProductSet (fun α => eL '' t α)`（[IUTchIII, Proposition 3.2, (i),
l.5724-5730] 第二 display）。缩减点 R9：fibre 级腿为 ℚ-线性等价；此处腿取环等价，
以使 R2 乘法模型下的乘积像交换。 -/
theorem sourceLogShell_tensorChain_image_comp {K K' K'' : Type*}
    [Field K] [CharZero K] [Field K'] [CharZero K'] [Field K''] [CharZero K'']
    {A : Type*} [Fintype A] (eL : K ≃+* K') (eR : K' ≃+* K'') (t : A → Set K) :
    eR '' (eL '' sourceLogShellTensorProductSet t) =
      sourceLogShellTensorProductSet (fun α => (eL.trans eR) '' t α) := by
  rw [sourceLogShell_prod_image_ringEquiv eL t,
    sourceLogShell_prod_image_ringEquiv eR (fun α => eL '' t α)]
  congr 1
  funext α
  rw [Set.image_image]
  rfl

/-- 张量层链的供给：两条乘性腿 `K →* K' →* K''`（R2 乘法模型的链腿形状，
缩减点 R9；与 fibre 层 `SourceLogShellXMuChainSupply` 的 ℚ-线性腿分列）。 -/
structure SourceLogShellXMuTensorChainSupply (K K' K'' : Type*)
    [Field K] [CharZero K] [Field K'] [CharZero K'] [Field K''] [CharZero K''] where
  leftEquiv : K ≃+* K'
  rightEquiv : K' ≃+* K''

namespace SourceLogShellXMuTensorChainSupply

variable {K K' K'' : Type*} [Field K] [CharZero K] [Field K'] [CharZero K']
  [Field K''] [CharZero K'']

/-- 张量层复合腿（原文两段链的复合）。 -/
def chainEquiv (S : SourceLogShellXMuTensorChainSupply K K' K'') : K ≃+* K'' :=
  S.leftEquiv.trans S.rightEquiv

/-- 张量层链式复合（原文 l.5724-5730 第二 display 的缩减形）：先左腿再右腿的像
= 复合腿的像。 -/
theorem chain_image_comp (S : SourceLogShellXMuTensorChainSupply K K' K'')
    {A : Type*} [Fintype A] (t : A → Set K) :
    S.rightEquiv '' (S.leftEquiv '' sourceLogShellTensorProductSet t) =
      sourceLogShellTensorProductSet (fun α => S.chainEquiv '' t α) :=
  sourceLogShell_tensorChain_image_comp S.leftEquiv S.rightEquiv t

end SourceLogShellXMuTensorChainSupply

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：×μ 中间包与三向 poly-iso 链（义务 `IUT-II.vertical-log-kummer` 的卡-D 缺口，
卡-C 剩余卡 3 的组装件）。 -/
def sourceLogShellXMuPacket : Obligation :=
  { id := "IUT-II.source-log-shell-xmu-packet"
    source := "IUT III, Proposition 3.2, (i) (text l.5706-5739); " ++
      "chain source: Proposition 1.2, (vi) (l.1900-1949) and (vii) (l.1950-1999)"
    status := VerificationStatus.conditional
    note :=
      "Times-mu intermediate packet and the three-way poly-isomorphism chain, " ++
        "reduced pass. Proved: the middle-packet carrier IQ((F-dash-times-mu)-vQ) with " ++
        "decomposition/membership/summand laws; conditional chain supply " ++
        "(left/right legs as single Q-linear equivalences with logShell-image " ++
        "compatibility); fibre-level composite preservation of logShell and IQSpan; " ++
        "vQ-packet composite image law assembled from the card-C transport laws " ++
        "through the explicit middle packet; single-summand pointwise compatibility; " ++
        "tensor-layer chain composite (ring-leg form). Reductions (labeled): R1-R5 " ++
        "inherited from card-C; R6 the functorial algorithms / Ism-orbits are carried " ++
        "as gate fields (no source layer for the F-dash-times-mu data yet); R7 " ++
        "action/log-volume compatibility not formalized; R8 archimedean case not " ++
        "formalized; R9 tensor-layer legs are ring equivalences (multiplicative " ++
        "collapsed model). The mixed packet log(A, alpha D-dash_v) remains an open card."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-carrier",
        "IUT-II.source-log-shell-iq-tensor-packet" ] }

end LeanFormal.IUT.Audit
