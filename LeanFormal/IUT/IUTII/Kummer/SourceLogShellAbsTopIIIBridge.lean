/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCodomainClosure

/-!
# IUT-II log-shell 载体层：[AbsTopIII] 层桥接卡（不变像等同）的缩减形式

本文件下钻 `SourceLogShellCodomainClosure.lean`（SHA256
`CE12CC99382EEC44805F0BF7B2B94BF73A59BDCA3159C2557C4553D01FF189AC`，冻结）§18
所列剩余卡「[AbsTopIII] 层桥接」：具体 `log_k(O^×_k)` 与抽象 pre-log-shell 像的等同
（即卡-A 缩减点 1 的正面对象）。

## 原文定位（冻结）

* [AbsTopIII, Definition 3.1, (iv)]（text l.3424-3520）：log-Frobenius 函子
  `logTF,TF`；pre-log-shell `λ(Π↷M) ⊆ logarith_TF,TF((Π↷M))`（l.3501-3520）——
  「the compact submodule of `k∼ =(O×_k)^pf` determined by the image of the subgroup
  `O×_k =(O×_k)^{Πk} ⊆O×_k` of Galois-invariants of `O×_k`」。
* [AbsTopIII, Definition 5.4, (iii)]（text l.7080-7110）：`p*_k := p_k`（`p_k` 奇）、
  `p_k²`（`p_k = 2`）；`pk`-进 log 给出双射 `1 + p*_k·O_k ≅→ p*_k·O_k`
  （l.7089-7093）；`O^{Πk}_{k∼} ⊆ I :=^def (p*_k)^{-1}·I* ⊆ (k∼)^{Πk}`（l.7094-7098），
  其中 `I*` 为 `O×_k =(O×_k)^{Πk}` 经由左侧纵向箭头的像——「in essence, the compact
  submodule constituted by the pre-log-shell discussed in Definition 3.1, (iv)」
  （l.7100-7105）；`I` 称为 `⃗Γ×_non` 的 log-shell；绝对非分歧且 `p_k` 奇时
  `O^{Πk}_{k∼} = I`（l.7108-7110）。
* [IUTchIII, Remark 1.2.2, (i)]（text l.2197-2222）：具体层 `k := K_v` 上
  `I_k :=^def (p*_v)^{-1}·log_k(O^×_k) ⊆ k`（l.2207-2215），evident inclusions
  `O^⊿_k ⊆ O_k ⊆ I_k; log_k(O^×_k) ⊆ I_k`（l.2216-2222）。
* 依赖链：`IUT-II.vertical-log-kummer`（pending）；`IUT-II.source-log-shell-carrier`
  （4A5414EA…）；`IUT-II.source-log-shell-codomain-closure`（CE12CC99…）。

## 冻结命题（对象/量词/假设/结论；缩减形式）

原命题（桥接）：具体 `log_k(O^×_k)` 与抽象 pre-log-shell 像在 `log` 下等同——
两者是同一个算术群 `O^×_k`（= 完备化 `(O^×_k)^pf` 的 Galois-不变子群）的两个化身。

缩减载体（`SourceLogShellDatum`）对应：`unitLayer`（全部单位在 `logMap` 下的像，
代表具体侧 `log_k(O^×_k)`）与 `preLogShell`（不变量子幺半群在 `logMap` 下的像，
代表抽象侧 pre-log-shell）在 `K` 中的相等：

  `SourceLogShellInvariantImageIdentification D : Prop := D.unitLayer = D.preLogShell`

单向 `preLogShell ⊆ unitLayer` 无条件成立（冻结载体 l.172）；故该卡等价于反方向
含入 `unitLayer ⊆ preLogShell`（每个单位的 log 都落在不变量像中）。这一半在缩减载体
中不可推——原文依赖算术事实 `(O^×_k)^pf^{Πk} = O^×_k`（完备化的 Galois-不变量 =
原单位群）与 `log_k` 的传输，均属 [AbsTopIII] 算术内容；故取为具名卡（路线①）。

## 路线与缩减点（显式标注）

1. 条件形：具名卡 + 由它推出的定理链（⇒ `codomainKummerContained`；⇒ 具体层
   `I_k = (p*_v)^{-1}·log_k(O^×_k)` 的载体形式 `logShell = (p*_v)^{-1}·unitLayer`；
   ⇒ 消费者三组装）；注入情形下该卡 ⇔「全部单位不变」，即上述算术事实的载体形状。
2. 精确负结果：两个格模型证明该卡与闭包机制（`SourceLogShellPowStable` 等）双向独立
   （`PStarMultiples`：`PowStable` 成立但等同失败；`CollapsedLog`：等同成立但
   `PowStable` 失败）。
3. 最小实现规格：完整 [AbsTopIII] 桥接所需缺失 API 清单见文末注记；未实现，不计已证。

## 缩减点（不得顶替原命题）

1. 算术事实 `(O^×_k)^pf^{Πk} = O^×_k` 与 `log_k` 在完备化上的传输不形式化；本文件把
   桥接的结论（像等同）作为具名条件，并证明其在缩减载体内的等价形状、保守后果与独立性。
2. 模型（`PStarMultiples`、`CollapsedLog`）为检验性构造，非原文对象。
-/

namespace LeanFormal.IUT

/-- [AbsTopIII] 层桥接卡（缩减形式）：具体侧单位像与抽象侧不变量像在载体中相等，
`unitLayer = preLogShell`——「具体 `log_k(O^×_k)` = 抽象 pre-log-shell 像」的载体化身。
对象：`D.unitLayer`、`D.preLogShell`；结论：相等；无附加假设（依赖链见文件头）。 -/
def SourceLogShellInvariantImageIdentification (D : SourceLogShellDatum) : Prop :=
  D.unitLayer = D.preLogShell

namespace SourceLogShellDatum

/-- 等同卡 ⇔ 反方向含入（正向 `preLogShell ⊆ unitLayer` 由冻结载体 l.172 无条件给出）。 -/
theorem invariantImageIdentification_iff_unitLayer_subset (D : SourceLogShellDatum) :
    SourceLogShellInvariantImageIdentification D ↔ D.unitLayer ⊆ D.preLogShell := by
  constructor
  · intro h a ha
    exact h ▸ ha
  · intro h
    exact Set.Subset.antisymm h D.preLogShell_subset_unitLayer

/-- 等同卡 ⇔ 逐单位形状：每个单位的 `log` 像都落在 pre-log-shell 中。 -/
theorem invariantImageIdentification_iff_forall_log_mem (D : SourceLogShellDatum) :
    SourceLogShellInvariantImageIdentification D ↔
      ∀ u : D.Units, (D.logMap u).toAdd ∈ D.preLogShell := by
  rw [invariantImageIdentification_iff_unitLayer_subset]
  constructor
  · intro h u
    exact h ⟨u, rfl⟩
  · intro h a ha
    obtain ⟨u, rfl⟩ := ha
    exact h u

/-- 主要保守后果：等同卡 ⇒ 值域含入 `codomainKummerContained`（`unitLayer ⊆ logShell`；
对比冻结闭包文件：那里经 `PowStable` 得到，这里经桥接卡得到）。 -/
theorem codomainKummerContained_of_invariantImageIdentification (D : SourceLogShellDatum)
    (h : SourceLogShellInvariantImageIdentification D) : D.codomainKummerContained := by
  intro a ha
  exact D.preLogShell_subset_logShell (h ▸ ha)

/-- 平凡充分条件：不变量取全部单位（校准模型形状）时等同卡成立。 -/
theorem invariantImageIdentification_of_invariants_eq_top (D : SourceLogShellDatum)
    (h : D.invariants = ⊤) : SourceLogShellInvariantImageIdentification D := by
  apply (invariantImageIdentification_iff_unitLayer_subset D).mpr
  intro a ha
  obtain ⟨u, rfl⟩ := ha
  exact ⟨u, by rw [h]; exact Submonoid.mem_top u, rfl⟩

/-- 在 `logMap` 注入（缩减载体中对应忽略 `μ_{p^∞}`-部分）时，等同卡 ⇔「全部单位都是
不变的」（`Units = invariants`）——即原文事实 `(O×_k)^pf^{Πk} = O×_k` 在载体内的形状；
说明该卡是算术内容而非代数重排。 -/
theorem invariantImageIdentification_iff_invariants_eq_top_of_injective
    (D : SourceLogShellDatum)
    (hinj : Function.Injective fun u : D.Units => (D.logMap u).toAdd) :
    SourceLogShellInvariantImageIdentification D ↔ D.invariants = ⊤ := by
  constructor
  · intro h
    have hcov : ∀ u : D.Units, (D.logMap u).toAdd ∈ D.preLogShell :=
      (invariantImageIdentification_iff_forall_log_mem D).mp h
    have hmem : ∀ u : D.Units, u ∈ D.invariants := by
      intro u
      obtain ⟨w, hw, hweq⟩ := hcov u
      have hwu : w = u := hinj hweq
      exact hwu ▸ hw
    exact le_antisymm le_top fun u _ => hmem u
  · intro h
    exact invariantImageIdentification_of_invariants_eq_top D h

/-- 具体层形状 `I_k = (p*_v)^{-1}·log_k(O^×_k)`（[IUTchIII, Remark 1.2.2, (i),
l.2207-2211]）的载体化身：`(p*_v)^{-1}` 乘以单位层。 -/
def invScaledUnitLayer (D : SourceLogShellDatum) : Set D.K :=
  {b | ∃ x ∈ D.unitLayer, (D.pStar : D.K)⁻¹ * x = b}

/-- 桥接卡的主要正面结论：`logShell`（经 pre-log-shell 定义）与
`(p*_v)^{-1}·unitLayer`（经具体单位像定义）在等同卡下重合——即载体中
「抽象定义的 log-shell = `(p*_v)^{-1}·log_k(O^×_k)`」。 -/
theorem logShell_eq_invScaledUnitLayer_of_invariantImageIdentification
    (D : SourceLogShellDatum)
    (h : SourceLogShellInvariantImageIdentification D) :
    D.logShell = D.invScaledUnitLayer := by
  rw [D.logShell_eq_invScaledPreLogShell]
  unfold SourceLogShellDatum.invScaledPreLogShell SourceLogShellDatum.invScaledUnitLayer
  rw [← h]

/-- 消费者组装①（Ind3）：桥接卡直接回填冻结文件的两条款 Kummer 像含入。 -/
theorem kummerImages_mem_logShell_of_invariantImageIdentification
    (D : SourceLogShellDatum) (h : SourceLogShellInvariantImageIdentification D) :
    (∀ u ∈ D.invariants, (D.logMap u).toAdd ∈ D.logShell) ∧
      (∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell) :=
  D.kummerImages_mem_logShell (D.codomainKummerContained_of_invariantImageIdentification h)

/-- 消费者组装②（Card-APT）：桥接卡经 `codomainKummerContained` 组装冻结结构
`NonarchimedeanLogKummerUpperSemi`。 -/
def toNonarchimedeanUpperSemi_of_invariantImageIdentification
    (D : SourceLogShellDatum) (h : SourceLogShellInvariantImageIdentification D) :
    NonarchimedeanLogKummerUpperSemi :=
  D.toNonarchimedeanUpperSemi (D.codomainKummerContained_of_invariantImageIdentification h)

/-- 消费者组装③（Cor 3.12 log-volume 上界 / QCMP 度量传递）：桥接卡供给值域侧
前提，度量上界沿冻结接口传给全部 Kummer 像。 -/
theorem codomain_kummerImages_bounded_of_invariantImageIdentification
    (D : SourceLogShellDatum) (h : SourceLogShellInvariantImageIdentification D)
    (measure : D.K → ℝ) {hull : ℝ}
    (hshell : ∀ d, d ∈ D.logShell → measure d ≤ hull) :
    (∀ (_m : ℤ) (u : D.Units), measure ((D.logMap u).toAdd) ≤ hull) ∧
      (∀ {m m' : ℤ} (u w : D.Units), w = u → m < m' →
        measure ((D.logMap w).toAdd) ≤ hull) :=
  D.codomain_kummerImages_bounded
    (D.codomainKummerContained_of_invariantImageIdentification h) measure hshell

end SourceLogShellDatum

/-! ## 校准互印证（桥接卡在冻结校准模型上通过） -/

/-- 校准模型（`invariants = ⊤`）满足桥接卡。 -/
theorem sourceLogShellCalibration_invariantImageIdentification :
    SourceLogShellInvariantImageIdentification sourceLogShellCalibrationDatum :=
  SourceLogShellDatum.invariantImageIdentification_of_invariants_eq_top
    sourceLogShellCalibrationDatum rfl

/-! ## 独立性（精确负结果）：桥接卡与闭包机制双向独立

模型均为检验性构造（非原文对象），沿用冻结文件的 `ℤ ↪ ℚ` 级 log
（`sourceLogShellScaledLatticeLogMap`，闭包文件 l.177）。 -/

/-- 模型 A（`PStarMultiples`）的不变量子幺半群：加法侧 `4ℤ`。 -/
def sourceLogShellPStarMultiplesInvariants : Submonoid (Multiplicative ℤ) where
  carrier := {x | ∃ k : ℤ, x.toAdd = 4 * k}
  one_mem' := ⟨0, by rw [toAdd_one]; norm_num⟩
  mul_mem' := by
    rintro x y ⟨kx, hx⟩ ⟨ky, hy⟩
    refine ⟨kx + ky, ?_⟩
    rw [toAdd_mul, hx, hy]
    ring

/-- 模型 A：`p = 2`（`p* = 4`）、`Units = Multiplicative ℤ`、不变量 = `4ℤ`、
`log` = 冻结 `ℤ ↪ ℚ`。 -/
def sourceLogShellPStarMultiplesDatum : SourceLogShellDatum where
  p := 2
  hp := Nat.prime_two
  K := ℚ
  Units := Multiplicative ℤ
  invariants := sourceLogShellPStarMultiplesInvariants
  logMap := sourceLogShellScaledLatticeLogMap

theorem sourceLogShellPStarMultiples_pStar_eq :
    sourceLogShellPStarMultiplesDatum.pStar = 4 := by decide

/-- 模型 A 满足 `PowStable`：每个单位的 `p* = 4` 次幂落在 `4ℤ` 内
（`toAdd (u^4) = 4·toAdd u`）。 -/
theorem sourceLogShellPStarMultiples_powStable :
    SourceLogShellPowStable sourceLogShellPStarMultiplesDatum := by
  intro u
  let v : Multiplicative ℤ := u
  change v ^ sourceLogShellPStarMultiplesDatum.pStar ∈
    sourceLogShellPStarMultiplesDatum.invariants
  rw [sourceLogShellPStarMultiples_pStar_eq]
  refine ⟨v.toAdd, ?_⟩
  rw [toAdd_pow, nsmul_eq_mul]
  norm_num

/-- 模型 A 经冻结闭包机制仍满足值域含入（机制侧不受桥接卡失败影响）。 -/
theorem sourceLogShellPStarMultiples_codomain_via_closure :
    sourceLogShellPStarMultiplesDatum.codomainKummerContained :=
  sourceLogShellPStarMultiplesDatum.codomainKummerContained_of_powStable
    sourceLogShellPStarMultiples_powStable

/-- 负结果 A：模型 A 上桥接卡失败（`log u = 1 ∈ unitLayer` 但 `1 ∉ 4ℤ = preLogShell`）
——`PowStable` 及闭包机制推不出 [AbsTopIII] 桥接。 -/
theorem sourceLogShellPStarMultiples_not_identification :
    ¬ SourceLogShellInvariantImageIdentification sourceLogShellPStarMultiplesDatum := by
  intro h
  have hsub := (SourceLogShellDatum.invariantImageIdentification_iff_unitLayer_subset
    sourceLogShellPStarMultiplesDatum).mp h
  have h1 : (1 : sourceLogShellPStarMultiplesDatum.K) ∈
      sourceLogShellPStarMultiplesDatum.unitLayer := by
    refine ⟨Multiplicative.ofAdd (1 : ℤ), ?_⟩
    change (sourceLogShellScaledLatticeLogMap (Multiplicative.ofAdd (1 : ℤ))).toAdd = (1 : ℚ)
    rw [sourceLogShellScaledLatticeLogMap_apply, toAdd_ofAdd]
    norm_num
  have hs : (1 : sourceLogShellPStarMultiplesDatum.K) ∈
      sourceLogShellPStarMultiplesDatum.preLogShell := hsub h1
  rw [SourceLogShellDatum.preLogShell, Set.mem_setOf_eq] at hs
  obtain ⟨w, hw, heq⟩ := hs
  let w' : Multiplicative ℤ := w
  obtain ⟨k, hk⟩ := hw
  have hkw : Multiplicative.toAdd w' = 4 * k := hk
  change (sourceLogShellScaledLatticeLogMap w').toAdd = (1 : ℚ) at heq
  have heqC : ((4 * k : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    calc ((4 * k : ℤ) : ℚ) = ((w'.toAdd : ℤ) : ℚ) := by rw [hkw]
      _ = (sourceLogShellScaledLatticeLogMap w').toAdd :=
        (sourceLogShellScaledLatticeLogMap_apply w').symm
      _ = (1 : ℚ) := heq
      _ = ((1 : ℤ) : ℚ) := by norm_num
  have hz : (4 : ℤ) * k = 1 := Int.cast_inj.mp heqC
  have hdvd : (4 : ℤ) ∣ 1 := ⟨k, hz.symm⟩
  norm_num at hdvd

/-! ## 模型 B（`CollapsedLog`）：等同卡成立但 `PowStable` 失败 -/

/-- 模型 B 的 log：常值 `1`（所有单位像坍缩到 `0`）。 -/
def sourceLogShellCollapsedLogMap : Multiplicative ℤ →* Multiplicative ℚ where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

/-- 模型 B：不变量 = `⊥`（平凡子幺半群）、`p = 2`、`log` = 常值。 -/
def sourceLogShellCollapsedLogDatum : SourceLogShellDatum where
  p := 2
  hp := Nat.prime_two
  K := ℚ
  Units := Multiplicative ℤ
  invariants := ⊥
  logMap := sourceLogShellCollapsedLogMap

theorem sourceLogShellCollapsedLog_pStar_eq :
    sourceLogShellCollapsedLogDatum.pStar = 4 := by decide

/-- 模型 B 上等同卡成立（两侧像均坍缩为 `{0}`）。 -/
theorem sourceLogShellCollapsedLog_identification :
    SourceLogShellInvariantImageIdentification sourceLogShellCollapsedLogDatum := by
  apply (SourceLogShellDatum.invariantImageIdentification_iff_unitLayer_subset
    sourceLogShellCollapsedLogDatum).mpr
  intro a ha
  obtain ⟨u, rfl⟩ := ha
  change (1 : Multiplicative ℚ).toAdd ∈ sourceLogShellCollapsedLogDatum.preLogShell
  rw [toAdd_one]
  exact sourceLogShellCollapsedLogDatum.zero_mem_preLogShell

/-- 负结果 B：模型 B 上 `PowStable` 失败（`u = ofAdd 1`，`u^4 ≠ 1`，而 `⊥ = {1}`）
——桥接卡推不出闭包条件；两张卡双向独立。 -/
theorem sourceLogShellCollapsedLog_not_powStable :
    ¬ SourceLogShellPowStable sourceLogShellCollapsedLogDatum := by
  intro h
  have hmem := h (Multiplicative.ofAdd (1 : ℤ))
  rw [sourceLogShellCollapsedLog_pStar_eq] at hmem
  change (Multiplicative.ofAdd (1 : ℤ)) ^ 4 ∈ (⊥ : Submonoid (Multiplicative ℤ)) at hmem
  rw [Submonoid.mem_bot] at hmem
  have hpow : (Multiplicative.ofAdd (1 : ℤ)) ^ 4 ≠ (1 : Multiplicative ℤ) := by
    intro hc
    have h1 := congrArg Multiplicative.toAdd hc
    rw [toAdd_pow, toAdd_ofAdd, toAdd_one] at h1
    norm_num at h1
  exact hpow hmem

/-! ## 最小实现规格（路线③；未实现，不计为已证）

完整 [AbsTopIII] 桥接（不把等同作为假设）所需的最小缺失 API：

1. 完备化单位的 Galois-不变量：载体需携带完备化 `(O×_k)^pf` 上的 `G_k`-作用
   （[AbsTopIII, Definition 3.1, (iv), l.3501-3520]），并证明不变量子群
   `(O×_k)^pf^{Πk} = O×_k`（Kummer 理论 + 分圆作用；Mathlib 现无 MLF 完备化的
   `G_k`-作用载体）。
2. p-进 log 的收敛双射：`1 + p*_k·O_k ≅→ p*_k·O_k`
   （[AbsTopIII, Definition 5.4, (iii), l.7089-7093]）及在 `O×_k` 上的传输；
   Mathlib 无 `p`-进 log 级数收敛载体。
3. log-Frobenius 传输：pre-log-shell `λ(Π↷M)` 作为 `k∼` 中紧子模经 `logk` 映到 `k`
   的像与具体 `logk(O×_k)` 的函子性等同（[AbsTopIII, Definition 5.4, (iii),
   l.7100-7107] 的 shell-arrow）。需要紧拓扑模/topological field API
   （沿用任务①§14 卡-B 记录）。

在以上 API 落地前，桥接保持为具名卡 `SourceLogShellInvariantImageIdentification`
（本文件给出其载体形状、保守后果与独立性证据）。 -/

namespace Audit

/-- 审计登记：[AbsTopIII] 层桥接卡的缩减形式（具名条件 + 保守后果 + 双向独立性）。 -/
def sourceLogShellAbsTopIIIBridge : Obligation :=
  { id := "IUT-II.source-log-shell-abstopiii-bridge"
    source := "AbsTopIII, Definition 3.1, (iv) (text l.3424-3520); " ++
      "Definition 5.4, (iii) (text l.7080-7110); IUT III, Remark 1.2.2, (i) " ++
      "(text l.2197-2222)"
    status := VerificationStatus.conditional
    note :=
      "Bridge card in reduced carrier form: the concrete unit image log_k(O^x_k) " ++
        "and the abstract pre-log-shell image (Galois-invariant units) are identified " ++
        "as SourceLogShellInvariantImageIdentification (unitLayer = preLogShell); " ++
        "preLogShell <= unitLayer is unconditional (frozen carrier), so the card is " ++
        "the converse inclusion; equivalent to forall-u log-membership; implies " ++
        "codomainKummerContained and the concrete shape logShell = (p*_v)^{-1} * " ++
        "unitLayer (IUT III Remark 1.2.2, (i)); with injective logMap it is equivalent " ++
        "to Units = invariants, the carrier avatar of (O^x_k)^pf^{Pi_k} = O^x_k. " ++
        "Independence (both directions) proved by two lattice models: PowStable does " ++
        "not imply the identification (PStarMultiples model, codomain still holds via " ++
        "the closure route), and the identification does not imply PowStable " ++
        "(CollapsedLog model). The arithmetic facts (perfected invariants = units, " ++
        "p-adic log bijection 1 + p* O -> p* O, log-Frobenius transport) remain a card " ++
        "with minimal spec listed in the file."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-carrier",
        "IUT-II.source-log-shell-codomain-closure" ] }

end Audit

end LeanFormal.IUT
