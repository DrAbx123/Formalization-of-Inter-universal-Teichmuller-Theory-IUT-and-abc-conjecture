/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# IUT-II log-shell 载体层：值域含入 `log_v(O^×_{Kv}) ⊆ I_v` 的机制化（卡-A 续）

本文件续接 `SourceLogShellCarrier.lean`（SHA256
`4A5414EA0704F6BAF860A7331F8A53E03931684F3452D902C7DA01647234113B`，冻结）的 §14
卡-A：把「log-shell 同时包含 log-link 值域侧 Kummer 同构的像」，即
`log_v(O^×_{Kv}) ⊆ I_v`（[IUTchIII, 引言, l.220-226]；[Remark 1.2.2, (i)]）的
**可形式化机制**抽成具名条件并证明定理链；并用两个模型（校准互印证 + 反例）界定
该类条件的强度。

## 原文定位（冻结）

* [IUTchIII, Remark 1.2.2, (i)]（text l.2197-2222）：具体层 `k := K_v` 上
  `I_k =^def (p*_v)^{-1}·log_k(O^×_k) ⊆ k`（l.2205-2215），且给出「evident
  inclusions」`O^⊿_k ⊆ O_k ⊆ I_k; log_k(O^×_k) ⊆ I_k`（l.2216-2222）。
  值域侧含入的机制：`O^×_k` 是群、对 `p*_v`-幂封闭 ⇒
  `p*_v·log_k(u) = log_k(u^{p*_v}) ∈ log_k(O^×_k)` ⇒
  `log_k(u) ∈ (p*_v)^{-1}·log_k(O^×_k) = I_k`。
* [IUTchIII, Definition 1.1, (i)]（l.1336-1351）：`p*_v := p_v`（`p_v` 奇）、
  `p_v²`（`p_v` 偶）；log-shell = pre-log-shell 乘因子 `(p*_v)^{-1}`。
* [IUTchIII, 引言, l.220-226]：`I_v` 同时包含 log-link 定义域与值域两侧 Kummer
  同构的像；抽象层（`Ψ~`）侧的桥接引 [AbsTopIII]。
* [IUTchII, Example 1.8, (ix)]（text l.2359-2366）：`I(G)` = 「`p^{-1}` 乘以
  `G`-不变 `O^×(G)` 在 `O^×μ(G)` 中的像」的 log-shell 版本。

## 机制与条件（显式标注为缩减形式）

冻结载体的 `codomainKummerContained := D.unitLayer ⊆ D.logShell` 在任意合同 hom
`logMap` 上不可推（卡-A）。本文件给出其充分条件：

* `SourceLogShellPowStable D := ∀ u, u ^ D.pStar ∈ D.invariants` —— 具体层
  「`O^×` 对 `p*_v`-幂封闭」在缩减载体上的形体（`p*` 幂后落在不变量子幺半群）；
* `SourceLogShellPrimePowStable D := ∀ u, u ^ D.p ∈ D.invariants` ——
  「p-幂分析」的可形式化残形（一次 `p_v`-幂即入不变量）；
  `powStable_of_primePowStable` 证明它足以推出 `PowStable`。

主链：`PrimePowStable ⇒ PowStable ⇒ codomainKummerContained ⇒ 两条款 Kummer 像
含入 / 冻结接口组装 / 度量上界传递`。
`codomainKummerContained_iff_powStar_log_mem` 给出一般充要刻画（目标形状）。
反例模型（scaled lattice，非原文对象）证明更弱的 `N = p*_v·2` 倍数稳定条件不足，
锁定该类机制的条件强度下界。

## 缩减点（不得顶替原命题）

1. [AbsTopIII] 的具体层 p-进分析（`O^×` 的高 p 幂落入 `1 + p^m O` 等）与抽象层
   `Ψ~` 的桥接不形式化；本文件把它约化为 `PrimePowStable`/`PowStable` 具名条件
   （充分条件，非等价；原命题未证部分仍为卡）。
2. 校准与反例模型均为检验性构造，非原文对象。
-/

namespace LeanFormal.IUT

/-- 具名条件（卡-A 充分条件）：`Units` 对 `p*_v`-幂封闭，即每个单位的 `p*_v`-幂
落在不变量子幺半群内。对应具体层「`O^×` 对 `p*_v`-幂封闭」
（[IUTchIII, Remark 1.2.2, (i), l.2216-2222]）。 -/
def SourceLogShellPowStable (D : SourceLogShellDatum) : Prop :=
  ∀ u : D.Units, u ^ D.pStar ∈ D.invariants

/-- 具名条件（更贴「p-幂分析」的语汇）：每个单位的一次 `p_v`-幂即落入不变量
子幺半群。由不变量子幺半群的幂封闭性可得 `SourceLogShellPowStable`
（因 `p*_v ∈ {p_v, p_v²}`）。 -/
def SourceLogShellPrimePowStable (D : SourceLogShellDatum) : Prop :=
  ∀ u : D.Units, u ^ D.p ∈ D.invariants

namespace SourceLogShellDatum

/-- `PrimePowStable ⇒ PowStable`：`p*_v = p_v`（`p_v` 奇）或 `p*_v = p_v²`
（`p_v` 偶）；偶情形由 `(u^{p_v})^{p_v} = u^{p_v·p_v}` 与不变量子幺半群的幂
封闭性得到。 -/
theorem powStable_of_primePowStable (D : SourceLogShellDatum)
    (h : SourceLogShellPrimePowStable D) : SourceLogShellPowStable D := by
  intro u
  have hpStar : D.pStar = D.p ∨ D.pStar = D.p * D.p := by
    unfold SourceLogShellDatum.pStar sourceLogShellStar
    by_cases hmod : D.p % 2 = 1
    · exact Or.inl (if_pos hmod)
    · exact Or.inr (if_neg hmod)
  rcases hpStar with h1 | h2
  · rw [h1]
    exact h u
  · rw [h2, pow_mul]
    exact D.invariants.pow_mem (h u) D.p

/-- 主机制（卡-A）：`p*` 幂封闭 ⇒ 值域含入 `unitLayer ⊆ logShell`。
`p*_v·log(u) = log(u^{p*_v})`（`logMap_pow_val`），而 `u^{p*_v} ∈ invariants`
保证 `log(u^{p*_v}) ∈ pre-log-shell`。 -/
theorem codomainKummerContained_of_powStable (D : SourceLogShellDatum)
    (h : SourceLogShellPowStable D) : D.codomainKummerContained := by
  intro a ha
  obtain ⟨u, rfl⟩ := ha
  rw [SourceLogShellDatum.logShell, Set.mem_setOf_eq]
  refine ⟨u ^ D.pStar, h u, ?_⟩
  rw [SourceLogShellDatum.logMap_pow_val, nsmul_eq_mul]

/-- `PrimePowStable` 版本（主链组合）。 -/
theorem codomainKummerContained_of_primePowStable (D : SourceLogShellDatum)
    (h : SourceLogShellPrimePowStable D) : D.codomainKummerContained :=
  D.codomainKummerContained_of_powStable (D.powStable_of_primePowStable h)

/-- 特例（对应具体层）：不变量取全体单位时，值域含入无条件成立——即具体层
`log_k(O^×_k) ⊆ I_k` 在「全部单位都不变」时的 evident 性
（[IUTchIII, Remark 1.2.2, (i), l.2216-2222]）。 -/
theorem codomainKummerContained_of_invariants_eq_top (D : SourceLogShellDatum)
    (h : D.invariants = ⊤) : D.codomainKummerContained :=
  D.codomainKummerContained_of_powStable fun u => by
    rw [h]
    exact Submonoid.mem_top u

/-- 一般充要刻画：值域含入 ⇔ 每个单位的 `p*_v`-幂的 log 落在 pre-log-shell
（等价于 `p*_v·log(u) ∈ pre-log-shell`）。这是 `codomainKummerContained` 在
`logMap_pow_val` 下的精确重述，也是任何充分条件的目标形状。 -/
theorem codomainKummerContained_iff_powStar_log_mem (D : SourceLogShellDatum) :
    D.codomainKummerContained ↔
      ∀ u : D.Units, (D.logMap (u ^ D.pStar)).toAdd ∈ D.preLogShell := by
  constructor
  · intro h u
    have h1 : (D.pStar : D.K) * (D.logMap u).toAdd ∈ D.preLogShell := h ⟨u, rfl⟩
    rwa [SourceLogShellDatum.logMap_pow_val, nsmul_eq_mul]
  · intro h a ha
    obtain ⟨u, rfl⟩ := ha
    have h1 : (D.pStar : D.K) * (D.logMap u).toAdd ∈ D.preLogShell := by
      have h2 := h u
      rwa [SourceLogShellDatum.logMap_pow_val, nsmul_eq_mul] at h2
    exact h1

/-- 消费者组装①：两条款 Kummer 像含入（冻结文件的 `kummerImages_mem_logShell`
经 `PowStable` 供给值域侧前提）。 -/
theorem kummerImages_mem_logShell_of_powStable (D : SourceLogShellDatum)
    (h : SourceLogShellPowStable D) :
    (∀ u ∈ D.invariants, (D.logMap u).toAdd ∈ D.logShell) ∧
      (∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell) :=
  D.kummerImages_mem_logShell (D.codomainKummerContained_of_powStable h)

/-- 消费者组装②：由 `PowStable` 直接组装任务①冻结结构（log-link 步在缩减载体上
取恒等对应，同冻结文件的 `toNonarchimedeanUpperSemi`）。 -/
def toNonarchimedeanUpperSemi_of_powStable (D : SourceLogShellDatum)
    (h : SourceLogShellPowStable D) : NonarchimedeanLogKummerUpperSemi :=
  D.toNonarchimedeanUpperSemi (D.codomainKummerContained_of_powStable h)

/-- 消费者组装③：度量上界传递（Cor 3.12 log-volume 上界 / Card-APT 形状），
值域侧前提由 `PowStable` 供给。 -/
theorem codomain_kummerImages_bounded_of_powStable (D : SourceLogShellDatum)
    (h : SourceLogShellPowStable D) (measure : D.K → ℝ) {hull : ℝ}
    (hshell : ∀ d, d ∈ D.logShell → measure d ≤ hull) :
    (∀ (_m : ℤ) (u : D.Units), measure ((D.logMap u).toAdd) ≤ hull) ∧
      (∀ {m m' : ℤ} (u w : D.Units), w = u → m < m' →
        measure ((D.logMap w).toAdd) ≤ hull) :=
  D.codomain_kummerImages_bounded (D.codomainKummerContained_of_powStable h)
    measure hshell

end SourceLogShellDatum

/-! ## 条件强度：更弱的倍数稳定条件不足（反例模型，非原文对象）

反例模型：`Units := Multiplicative ℤ`（加法侧 `ℤ`）、不变量取加法侧 `8ℤ`、
`logMap` 取自然注入 `ℤ ↪ ℚ`、`p = 2`（`p*_v = 4`）。该模型上
「每个单位的 `p*_v·2 = 8` 次幂落入不变量」成立（`8·(8ℤ) ⊆ 8ℤ` 的形体），
但 `codomainKummerContained` 失败（`log(u) = 1` 需 `4 ∈ 8ℤ`）——即
`N = p*_v·m`（`m ≥ 2`）型倍数稳定条件不足以支撑值域含入。 -/

/-- 反例模型的不变量子幺半群：加法侧 `8ℤ ⊆ ℤ`（作为 `Multiplicative ℤ` 的
子幺半群）。 -/
def sourceLogShellScaledLatticeInvariants : Submonoid (Multiplicative ℤ) where
  carrier := {x | ∃ k : ℤ, x.toAdd = 8 * k}
  one_mem' := ⟨0, by rw [toAdd_one]; norm_num⟩
  mul_mem' := by
    rintro x y ⟨kx, hx⟩ ⟨ky, hy⟩
    refine ⟨kx + ky, ?_⟩
    rw [toAdd_mul, hx, hy]
    ring

/-- 反例模型的 log：加法侧自然注入 `ℤ ↪ ℚ`。 -/
def sourceLogShellScaledLatticeLogMap : Multiplicative ℤ →* Multiplicative ℚ where
  toFun z := Multiplicative.ofAdd ((z.toAdd : ℚ))
  map_one' := by simp [toAdd_one]
  map_mul' z w := by
    rw [← ofAdd_add, toAdd_mul]
    push_cast
    rfl

/-- 反例模型的载体：`p = 2`、`K = ℚ`、`Units = Multiplicative ℤ`、
不变量 = `8ℤ`、log = 自然注入。 -/
def sourceLogShellScaledLatticeDatum : SourceLogShellDatum where
  p := 2
  hp := Nat.prime_two
  K := ℚ
  Units := Multiplicative ℤ
  invariants := sourceLogShellScaledLatticeInvariants
  logMap := sourceLogShellScaledLatticeLogMap

theorem sourceLogShellScaledLatticeModel_pStar_eq :
    sourceLogShellScaledLatticeDatum.pStar = 4 := by decide

theorem sourceLogShellScaledLatticeLogMap_apply (z : Multiplicative ℤ) :
    (sourceLogShellScaledLatticeLogMap z).toAdd = (z.toAdd : ℚ) := by
  simp [sourceLogShellScaledLatticeLogMap, toAdd_ofAdd]

/-- 反例模型中 `1 = log_k(ofAdd 1) ∈ unitLayer`（干净形式）。 -/
theorem sourceLogShellScaledLatticeModel_one_mem_unitLayer :
    (1 : ℚ) ∈ sourceLogShellScaledLatticeDatum.unitLayer := by
  refine ⟨Multiplicative.ofAdd (1 : ℤ), ?_⟩
  change (sourceLogShellScaledLatticeLogMap (Multiplicative.ofAdd (1 : ℤ))).toAdd =
    (1 : ℚ)
  rw [sourceLogShellScaledLatticeLogMap_apply, toAdd_ofAdd]
  norm_num

/-- 弱条件在反例模型上成立：每个单位的 `p*_v·2 = 8` 次幂落入不变量。 -/
theorem sourceLogShellScaledLatticeModel_doublePStarPow_mem :
    ∀ u : sourceLogShellScaledLatticeDatum.Units,
      u ^ (sourceLogShellScaledLatticeDatum.pStar * 2) ∈
        sourceLogShellScaledLatticeDatum.invariants := by
  intro u
  let v : Multiplicative ℤ := u
  change v ^ (sourceLogShellScaledLatticeDatum.pStar * 2) ∈
    sourceLogShellScaledLatticeDatum.invariants
  rw [sourceLogShellScaledLatticeModel_pStar_eq,
    show (4 : ℕ) * 2 = 8 by norm_num]
  refine ⟨v.toAdd, ?_⟩
  rw [toAdd_pow, nsmul_eq_mul]
  norm_num

/-- 反例模型上 `PowStable` 失败（`u = ofAdd 1` 时 `4 ∉ 8ℤ`）——弱条件确实严格弱。 -/
theorem sourceLogShellScaledLatticeModel_not_powStable :
    ¬ SourceLogShellPowStable sourceLogShellScaledLatticeDatum := by
  intro h
  let v : Multiplicative ℤ := Multiplicative.ofAdd (1 : ℤ)
  have hv : v ^ sourceLogShellScaledLatticeDatum.pStar ∈
      sourceLogShellScaledLatticeDatum.invariants := h v
  rw [sourceLogShellScaledLatticeModel_pStar_eq] at hv
  obtain ⟨k, hk⟩ := hv
  have hv4 : Multiplicative.toAdd (v ^ 4) = 4 := by
    change Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ 4) = 4
    rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
    norm_num
  rw [hv4] at hk
  have hdvd : (8 : ℤ) ∣ 4 := ⟨k, hk⟩
  norm_num at hdvd

/-- 但该模型上值域含入失败（`log(u) = 1 ∉ I`，因 `4 ∉ 8ℤ`）——弱条件不足。 -/
theorem sourceLogShellScaledLatticeModel_not_codomain :
    ¬ sourceLogShellScaledLatticeDatum.codomainKummerContained := by
  intro h
  have hshell : (1 : sourceLogShellScaledLatticeDatum.K) ∈
      sourceLogShellScaledLatticeDatum.logShell :=
    h sourceLogShellScaledLatticeModel_one_mem_unitLayer
  rw [SourceLogShellDatum.logShell, Set.mem_setOf_eq] at hshell
  rw [sourceLogShellScaledLatticeModel_pStar_eq, mul_one] at hshell
  obtain ⟨w, hw, heq⟩ := hshell
  let w' : Multiplicative ℤ := w
  obtain ⟨k, hk⟩ := hw
  have hkw : Multiplicative.toAdd w' = 8 * k := hk
  change (sourceLogShellScaledLatticeLogMap w').toAdd = (4 : ℚ) at heq
  rw [sourceLogShellScaledLatticeLogMap_apply, hkw] at heq
  have hdz : ((8 * k : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
    calc ((8 * k : ℤ) : ℚ) = (4 : ℚ) := heq
      _ = ((4 : ℤ) : ℚ) := by norm_num
  have hz4 : (8 * k : ℤ) = 4 := Int.cast_inj.mp hdz
  have hdvd : (8 : ℤ) ∣ 4 := ⟨k, hz4.symm⟩
  norm_num at hdvd

/-! ## 校准互印证（条件在冻结校准模型上通过，经新主链重得冻结结论） -/

/-- 校准模型（`invariants = ⊤`）满足 `PrimePowStable`（平凡）。 -/
theorem sourceLogShellCalibration_primePowStable :
    SourceLogShellPrimePowStable sourceLogShellCalibrationDatum :=
  fun _ => Submonoid.mem_top _

/-- 经新主链在新文件内重得冻结校准结论 `codomainKummerContained`
（与 `SourceLogShellCarrier.lean` 中的直接证明互为印证）。 -/
theorem sourceLogShellCalibration_codomainKummerContained_via_closure :
    sourceLogShellCalibrationDatum.codomainKummerContained :=
  sourceLogShellCalibrationDatum.codomainKummerContained_of_primePowStable
    sourceLogShellCalibration_primePowStable

namespace Audit

/-- 审计登记：值域含入机制化（卡-A 续：充分条件链 + 充要刻画 + 强度反例）。 -/
def sourceLogShellCodomainClosure : Obligation :=
  { id := "IUT-II.source-log-shell-codomain-closure"
    source := "IUT III, Remark 1.2.2, (i) (text l.2197-2222); Introduction l.220-226; " ++
      "Definition 1.1, (i) (l.1336-1351); IUT II, Example 1.8, (ix) (text l.2359-2366)"
    status := VerificationStatus.conditional
    note :=
      "Card-A mechanism closure, reduced pass. Proved on the frozen carrier " ++
        "(SourceLogShellCarrier.lean): SourceLogShellPowStable (carrier form of the " ++
        "concrete-level p*_v-power closure of O^x in Remark 1.2.2, (i)) implies " ++
        "codomainKummerContained via p*_v * log u = log (u^p*_v); " ++
        "SourceLogShellPrimePowStable (single p_v-power closure, the formalizable " ++
        "residue of the p-adic power analysis) implies PowStable via " ++
        "p*_v = p_v or p_v^2; the characterization " ++
        "codomainKummerContained_iff_powStar_log_mem holds unconditionally; " ++
        "invariants = top case recovers the concrete-layer evident inclusion; " ++
        "consumer assemblies (two-clause Kummer images, frozen upper-semi " ++
        "assembly, measure-bound transport) are re-derived from PowStable; " ++
        "the Q/v_2 calibration passes the condition and rederives the frozen " ++
        "calibration theorem through the new chain; the scaled-lattice model " ++
        "(not a paper object) shows the weaker N = p*_v * 2 multiple stability " ++
        "is insufficient. The [AbsTopIII]-level bridging (identification of the " ++
        "concrete log_k(O^x_k) with the abstract pre-log-shell image) remains a " ++
        "card, not formalized."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-carrier" ] }

end Audit

end LeanFormal.IUT
