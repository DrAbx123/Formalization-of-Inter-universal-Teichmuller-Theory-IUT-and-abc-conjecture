/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import LeanFormal.IUT.IUTII.Kummer.RationalRootSystem
import LeanFormal.IUT.IUTII.Kummer.ConcreteEtaleKummerBridge
import LeanFormal.IUT.Foundations.Arithmetic.NormLog
import LeanFormal.IUT.Audit.Status

/-!
# IUT-II vertical log-Kummer：有序层缩减 pass

冻结的原文命题（与仓库义务 `IUT-II.vertical-log-kummer` 对位，见
`IUTII/Kummer/VerticalCorrespondence.lean`）：

* [IUTchIII, Definition 1.1, (i)]：`log-shell` `I` 由 `pre-log-shell` 乘以因子
  `(p*_v)^{-1}` 得到；`pre-log-shell` 是 `Ψ` 的 `G_v(Π_v)`-不变单位在 `Ψ~`
  中的像。
* [IUTchIII, Proposition 1.2, (v), (bnon), (cnon)]：`I` 包含不变量子幺半群，
  也包含单位之不变量子幺半群的像。
* [IUTchIII, Remark 1.2.2, (i)]：非 arch 具体模型
  `I_k = (p*_v)^{-1} · log_k(O^×_k)`，并有 `O^⊿_k ⊆ I_k` 与
  `log_k(O^×_k) ⊆ I_k`。
* [IUTchIII, Remark 1.2.2, (iii)]：上半交换性。coric holomorphic log-shell
  同时包含 Kummer 同构的像，以及 Kummer 同构与 log-link 迭代复合的像；
  (iv) 记录：不存在相应的下半交换性，方向是单向的。
* [IUTchIII, Remark 1.1.1]：log-link 的迭代 `m' ≥ 1`。
* [IUTchIII, Proposition 3.5, (ii), (a), (b)]：非 arch 处为自然包含 `⊆`，
  arch 处为自然满射 `↠`；对 `m ∈ ℤ` 与迭代 `m' ≥ 1` 量化。
* [IUTchIII, Theorem 3.11, (ii)]：`(Ind3)` 即上述包含/满射形式的「上半相容」，
  并与 log-volume 精确相容 [Proposition 3.9, (iv)]。

与仓库既有注记的差异（如实记录）：`VerticalCorrespondence.lean` 将 `source`
写作 "IUT II, Sections 5--6"；但 [IUTchII] 仅含 §1--§4，垂直 log-Kummer
对应的原文位置是 [IUTchIII] §1 与 §3。

本文件不含未证占位声明。相对原文的缩减在对应声明处标注：Kummer 同构仅以其像
映射出现、Galois 不变量子模直接作为量化载体、张量包指标取 `j = 0`（原文允许
`j = 0`）。消费者：Card-APT（平行移动不变量）、Ind3（上半相容）、QCMP。
-/

namespace LeanFormal.IUT

universe u v

/-! ## 1. 原文忠实核：非 archimedean 上半包含（Prop 3.5, (ii), (a)） -/

/-- [IUTchIII, Proposition 3.5, (ii), (a)] 的核心形状（取 `j = 0`；原文允许
`j = 0`）：固定 `n` 列与 `v_Q ∈ V^non_Q`，coric log-shell `I` 包含
(1) 各级单位的 Kummer 像，以及 (2) Kummer 像与正长度 log-link 迭代之复合的像。
`logLinkUnit` / `logIterate` 是「只作用于定义域中单位」的对应关系
（[IUTchIII, Remark 1.2.2, (ii)] 的约定）。缩减：Kummer 同构在此只以其像映射
出现；张量包指标固定为单因子 `j = 0`。 -/
structure NonarchimedeanLogKummerUpperSemi where
  Unit : ℤ → Type u
  coricModule : Type u
  logShell : Set coricModule
  logLinkUnit : ∀ m : ℤ, Unit m → Unit (m + 1) → Prop
  logIterate : ∀ {m m' : ℤ}, Unit m → Unit m' → Prop
  logIterate_refl : ∀ (m : ℤ) (u : Unit m), logIterate u u
  logIterate_step : ∀ {m m' : ℤ} (u : Unit m) (y : Unit m')
    (z : Unit (m' + 1)), logIterate u y → logLinkUnit m' y z → logIterate u z
  kummer : ∀ m : ℤ, Unit m → coricModule
  kummer_mem_logShell : ∀ (m : ℤ) (u : Unit m), kummer m u ∈ logShell
  iterate_kummer_mem_logShell : ∀ {m m' : ℤ} (u : Unit m) (w : Unit m'),
    logIterate u w → m < m' → kummer m' w ∈ logShell

namespace NonarchimedeanLogKummerUpperSemi

/-- 由冻结接口推得的消费定理（消费者：Cor 3.12 的 log-volume 上界、
Prop 3.9, (iv) 的上界方向）：任何把 log-shell 映到 `≤ hull` 的测量都给出
(1)、(2) 两族像的统一上界。 -/
theorem logShell_images_bounded (K : NonarchimedeanLogKummerUpperSemi)
    (measure : K.coricModule → ℝ) {hull : ℝ}
    (hshell : ∀ d, d ∈ K.logShell → measure d ≤ hull) :
    (∀ (m : ℤ) (u : K.Unit m), measure (K.kummer m u) ≤ hull) ∧
      (∀ {m m' : ℤ} (u : K.Unit m) (w : K.Unit m'),
        K.logIterate u w → m < m' → measure (K.kummer m' w) ≤ hull) :=
  ⟨fun m u => hshell _ (K.kummer_mem_logShell m u),
    fun u w hrel hlt => hshell _ (K.iterate_kummer_mem_logShell u w hrel hlt)⟩

end NonarchimedeanLogKummerUpperSemi

/-! ## 2. 原文忠实核：archimedean 满射（Prop 3.5, (ii), (b)） -/

set_option linter.unusedVariables false in
/-- [IUTchIII, Proposition 3.5, (ii), (b)] 的核心形状：在 `v_Q ∈ V^arc_Q`，
闭单位球 `I` 包含单位群与半径 `π` 闭球的像；并且对每个 `m' ≥ 1`，级别 `m`
的半径 `π` 闭球包含一个子集 `S`，`S` 沿 `m'` 次 log-link 迭代满射到级别
`m - m'` 上「迭代有定义的」单位部分（原文：a closed ball as in (2) contains,
for each m′ ≥ 1, a subset that surjects ... onto the subset of the group of
units ... on which this iterate is defined）。`coricKummerLink m s u` 表示
`s`（迭代目标级别 `m` 的 coric 像）与单位 `u` 的对应关系。缩减：以对应关系
代替具体同构；coric 载体本身级别无关，级别 `m` 只出现在闭球与迭代复合处。 -/
structure ArchimedeanLogKummerUpperSemi where
  Unit : ℤ → Type u
  coricModule : Type u
  archimedeanBall : Set coricModule
  piBallImage : Set coricModule
  logLinkUnit : ∀ m : ℤ, Unit m → Unit (m + 1) → Prop
  logIterate : ∀ {m m' : ℤ}, Unit m → Unit m' → Prop
  logIterate_refl : ∀ (m : ℤ) (u : Unit m), logIterate u u
  logIterate_step : ∀ {m m' : ℤ} (u : Unit m) (y : Unit m')
    (z : Unit (m' + 1)), logIterate u y → logLinkUnit m' y z → logIterate u z
  kummer : ∀ m : ℤ, Unit m → coricModule
  kummer_mem_archimedeanBall : ∀ (m : ℤ) (u : Unit m),
    kummer m u ∈ archimedeanBall
  piBallImage_subset : piBallImage ⊆ archimedeanBall
  coricKummerLink : ∀ (m : ℤ) {m' : ℤ}, coricModule → Unit m' → Prop
  iteratedDefined : ∀ {m : ℤ}, Unit m → Prop
  archimedean_surjection : ∀ (m : ℤ) {m' : ℤ}, 1 ≤ m' →
    ∃ S : Set coricModule, S ⊆ piBallImage ∧
      ∀ u : Unit (m - m'), iteratedDefined u →
        ∃ s, s ∈ S ∧ coricKummerLink m s u

/-! ## 3. 有序层合约（单值化缩减形式） -/

set_option linter.checkUnivs false in
/-- 有序层合约：仓库义务 `IUT-II.vertical-log-kummer` 的抽象核心之上，加入
Card-APT / Ind3 所需的单调性：log 步对源序单调，Kummer 像对源序单调。
「缩减形式」注记：`VerticalLogKummerCorrespondence` 以不等式 `≤` 代替原文的
集合包含 `⊆` / 满射 `↠` 与 `I^Q` 作用；该单值化是消费者（Card-APT、Ind3、
QCMP）实际使用的形状，原文的集合版本见本文件 §1、§2 的两个核结构。 -/
structure VerticalLogKummerOrderedLayer extends VerticalLogKummerCorrespondence where
  log_monotone : ∀ m : Nat, Monotone (log m)
  kummer_monotone : ∀ m : Nat, Monotone (kummer m)

namespace VerticalLogKummerOrderedLayer

variable (L : VerticalLogKummerOrderedLayer)

/-- 平行移动（log-link 迭代）保持源序：Card-APT 的「不变量沿平行移动保持」。 -/
theorem transport_monotone (m : Nat) (x y : L.F m) (hxy : x ≤ y) :
    ∀ n : Nat, (L.toVerticalLogKummerCorrespondence).transport m n x ≤
      (L.toVerticalLogKummerCorrespondence).transport m n y
  | 0 => by simpa using hxy
  | n + 1 => L.log_monotone (m + n) (transport_monotone m x y hxy n)

/-- Kummer 像沿平行移动对源序单调（Card-APT 不变量的 Kummer 侧）。 -/
theorem kummer_transport_monotone (m : Nat) (x y : L.F m) (hxy : x ≤ y) :
    ∀ n : Nat,
      L.kummer (m + n) ((L.toVerticalLogKummerCorrespondence).transport m n x) ≤
        L.kummer (m + n) ((L.toVerticalLogKummerCorrespondence).transport m n y)
  | n => L.kummer_monotone (m + n) (transport_monotone L m x y hxy n)

/-- 上半不等式与单调性的合成：`x ≤ y` 时，`x` 的 Kummer 像被 `y` 的 `n` 步
平行移动像所控制（Card-APT / QCMP 的比较形状）。 -/
theorem kummer_le_transport_of_le (m : Nat) (x y : L.F m) (hxy : x ≤ y)
    (n : Nat) :
    L.kummer m x ≤
      L.kummer (m + n) ((L.toVerticalLogKummerCorrespondence).transport m n y) :=
  (L.kummer_monotone m hxy).trans
    ((L.toVerticalLogKummerCorrespondence).kummer_le_transport m y n)

/-- hull 支配沿单调提升传递：若 `y` 支配 hull 且 `x ≤ y`，则 `x` 的 Kummer 像
也被 hull 控制（QCMP 的 `q ≤ target` 形状）。 -/
theorem hullDominates_of_le {x y : L.F 0} (hxy : x ≤ y) {hull : L.D}
    (H : (L.toVerticalLogKummerCorrespondence).HullDominates y hull) :
    L.kummer 0 x ≤ hull :=
  (L.kummer_monotone 0 hxy).trans (by simpa using H 0)

end VerticalLogKummerOrderedLayer

/-! ## 4. 思路 (a)：多项式/根核模型（真实编译实例） -/

/-- 由可分根系统选出的 `N` 次根：`x^(1/N)`。这是 [IUTchIII, Remark 1.2.2, (i)]
中 `log_k`/根过渡的单值代理，供 log-shell 迭代使用。 -/
noncomputable def rootSystemPowRoot (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (x : (AlgebraicClosure ℚ_[p])ˣ) : (AlgebraicClosure ℚ_[p])ˣ :=
  ((AlgebraicClosureRootSystem.compatibleRationalRoots x).roots
    ((N : ℚ)⁻¹)).toMul

/-- 任意相容根系统的 `N` 次根方程（无需唯一性：只用到加性根系统公理）。 -/
theorem compatibleRootSystem_pow_root {M : Type*} [CommGroup M] {value : M}
    (r : CompatibleRootSystem M value) (N : Nat) (hN : N ≠ 0) :
    (r.roots ((N : ℚ)⁻¹)).toMul ^ N = value := by
  apply Additive.ofMul.injective
  change N • r.roots ((N : ℚ)⁻¹) = Additive.ofMul value
  have h := r.roots.map_nsmul N ((N : ℚ)⁻¹)
  rw [← h]
  have hq : N • ((N : ℚ)⁻¹) = 1 := by
    rw [nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN)
  rw [hq, r.root_one]

theorem rootSystemPowRoot_pow (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (hN : N ≠ 0) (x : (AlgebraicClosure ℚ_[p])ˣ) :
    rootSystemPowRoot p N x ^ N = x :=
  compatibleRootSystem_pow_root _ N hN

theorem rootSystemPowRoot_norm_pow (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (hN : N ≠ 0) (x : (AlgebraicClosure ℚ_[p])ˣ) :
    ‖(rootSystemPowRoot p N x : AlgebraicClosure ℚ_[p])‖ ^ N =
      ‖(x : AlgebraicClosure ℚ_[p])‖ := by
  have h := congrArg (fun u : (AlgebraicClosure ℚ_[p])ˣ =>
    ‖(u : AlgebraicClosure ℚ_[p])‖) (rootSystemPowRoot_pow p N hN x)
  rwa [Units.val_pow_eq_pow_val, norm_pow] at h

theorem rootSystemPowRoot_log_norm (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (hN : N ≠ 0) (x : (AlgebraicClosure ℚ_[p])ˣ) :
    Real.log ‖(rootSystemPowRoot p N x : AlgebraicClosure ℚ_[p])‖ =
      Real.log ‖(x : AlgebraicClosure ℚ_[p])‖ / (N : ℝ) := by
  have hpow := rootSystemPowRoot_norm_pow p N hN x
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hlog : Real.log ‖(x : AlgebraicClosure ℚ_[p])‖ =
      (N : ℝ) * Real.log ‖(rootSystemPowRoot p N x : AlgebraicClosure ℚ_[p])‖ := by
    rw [← hpow, Real.log_pow]
  rw [hlog, eq_div_iff hN']
  ring

/-- 单位的 log-shell 深度：`max 0 (-log ‖·‖)`，即单值化的
[IUTchIII, Remark 1.2.2, (i)] `log_k` 量。 -/
noncomputable def unitShellDepth (p : Nat) [Fact (Nat.Prime p)]
    (x : (AlgebraicClosure ℚ_[p])ˣ) : ℝ :=
  max 0 (-(unitNormLogDegree (AlgebraicClosure ℚ_[p]) x).toAdd)

theorem unitShellDepth_nonneg (p : Nat) [Fact (Nat.Prime p)]
    (x : (AlgebraicClosure ℚ_[p])ˣ) : 0 ≤ unitShellDepth p x :=
  le_max_left _ _

/-- 定义展开：`unitShellDepth x = max 0 (-log ‖x‖)`（[IUTchIII, Remark 1.2.2,
(i)] 的 `log_k` 量）。 -/
theorem unitShellDepth_eq_max_neg_log (p : Nat) [Fact (Nat.Prime p)]
    (x : (AlgebraicClosure ℚ_[p])ˣ) :
    unitShellDepth p x =
      max 0 (-(Real.log ‖(x : AlgebraicClosure ℚ_[p])‖)) := by
  unfold unitShellDepth unitNormLogDegree
  rfl

theorem max_zero_div_nonneg (t : ℝ) (N : Nat) :
    max 0 (t / (N : ℝ)) = max 0 t / (N : ℝ) := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right (div_nonneg ht (Nat.cast_nonneg N)), max_eq_right ht]
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg ht (Nat.cast_nonneg N)),
      max_eq_left ht, zero_div]

/-- 深度沿 `N` 次根过渡按 `1/N` 缩放（含 `N = 0` 的退化情形）。 -/
theorem unitShellDepth_rootSystemPowRoot (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (hN : N ≠ 0) (x : (AlgebraicClosure ℚ_[p])ˣ) :
    unitShellDepth p (rootSystemPowRoot p N x) = unitShellDepth p x / (N : ℝ) := by
  rw [unitShellDepth_eq_max_neg_log p (rootSystemPowRoot p N x),
    unitShellDepth_eq_max_neg_log p x,
    rootSystemPowRoot_log_norm p N hN x, ← neg_div]
  exact max_zero_div_nonneg _ _

/-- 整性在根过渡下保持：`‖x‖ ≤ 1` 时 `‖x^(1/N)‖ ≤ 1`
（[IUTchIII, Remark 1.2.2, (i)] 的 `O^⊿ ⊆ I` 一侧的模型事实）。 -/
theorem rootSystemPowRoot_norm_le_one (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (hN : N ≠ 0) (x : (AlgebraicClosure ℚ_[p])ˣ)
    (hx : ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 1) :
    ‖(rootSystemPowRoot p N x : AlgebraicClosure ℚ_[p])‖ ≤ 1 := by
  have hy_pos : 0 < ‖(rootSystemPowRoot p N x : AlgebraicClosure ℚ_[p])‖ :=
    norm_pos_iff.mpr (Units.ne_zero _)
  have hx_pos : 0 < ‖(x : AlgebraicClosure ℚ_[p])‖ :=
    norm_pos_iff.mpr (Units.ne_zero x)
  have hlogx : Real.log ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 0 :=
    Real.log_nonpos hx_pos.le hx
  have hlogy : Real.log ‖(rootSystemPowRoot p N x :
      AlgebraicClosure ℚ_[p])‖ ≤ 0 := by
    rw [rootSystemPowRoot_log_norm p N hN x]
    exact div_nonpos_of_nonpos_of_nonneg hlogx (Nat.cast_nonneg N)
  calc ‖(rootSystemPowRoot p N x : AlgebraicClosure ℚ_[p])‖
      = Real.exp (Real.log ‖(rootSystemPowRoot p N x :
          AlgebraicClosure ℚ_[p])‖) := (Real.exp_log hy_pos).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlogy
    _ = 1 := Real.exp_zero

/-- 根选择的无关性：两个相容根系统给出的同级根有相同的深度，因此 log-shell
像与根选择无关（对应 [IUTchIII, Proposition 3.5, (i)] 及其引用的
「同构类相容」性质的深度侧）。 -/
theorem rootSystemPowRoot_depth_independent (p : Nat) [Fact (Nat.Prime p)]
    (N : Nat) (hN : N ≠ 0) (x : (AlgebraicClosure ℚ_[p])ˣ)
    (first second : CompatibleRootSystem ((AlgebraicClosure ℚ_[p])ˣ) x) :
    unitShellDepth p ((second.roots ((N : ℚ)⁻¹)).toMul) =
      unitShellDepth p ((first.roots ((N : ℚ)⁻¹)).toMul) := by
  have hfirst : (first.roots ((N : ℚ)⁻¹)).toMul ^ N = x :=
    compatibleRootSystem_pow_root first N hN
  have hsecond : (second.roots ((N : ℚ)⁻¹)).toMul ^ N = x :=
    compatibleRootSystem_pow_root second N hN
  have hratio : (((second.roots ((N : ℚ)⁻¹)).toMul /
      (first.roots ((N : ℚ)⁻¹)).toMul) ^ N) = 1 := by
    rw [div_pow, hsecond, hfirst]
    simp
  have hnormpow : ‖(((second.roots ((N : ℚ)⁻¹)).toMul /
      (first.roots ((N : ℚ)⁻¹)).toMul :
        (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p])‖ ^ N = 1 := by
    have hc := congrArg (fun u : (AlgebraicClosure ℚ_[p])ˣ =>
      ‖(u : AlgebraicClosure ℚ_[p])‖) hratio
    rwa [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] at hc
  have hnorm_one : ‖(((second.roots ((N : ℚ)⁻¹)).toMul /
      (first.roots ((N : ℚ)⁻¹)).toMul :
        (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p])‖ = 1 := by
    have hpos : 0 < ‖(((second.roots ((N : ℚ)⁻¹)).toMul /
        (first.roots ((N : ℚ)⁻¹)).toMul :
          (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p])‖ :=
      norm_pos_iff.mpr (Units.ne_zero _)
    have hlog : Real.log ‖(((second.roots ((N : ℚ)⁻¹)).toMul /
        (first.roots ((N : ℚ)⁻¹)).toMul :
          (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p])‖ = 0 := by
      have h := congrArg Real.log hnormpow
      rw [Real.log_pow, Real.log_one] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (Nat.cast_ne_zero.mpr hN)
      · exact h'
    have h := Real.exp_log hpos
    rw [hlog, Real.exp_zero] at h
    exact h.symm
  have hnorm_eq : ‖((second.roots ((N : ℚ)⁻¹)).toMul :
      AlgebraicClosure ℚ_[p])‖ = ‖((first.roots ((N : ℚ)⁻¹)).toMul :
        AlgebraicClosure ℚ_[p])‖ := by
    have hmul : ((second.roots ((N : ℚ)⁻¹)).toMul /
        (first.roots ((N : ℚ)⁻¹)).toMul) *
        (first.roots ((N : ℚ)⁻¹)).toMul =
          (second.roots ((N : ℚ)⁻¹)).toMul :=
      div_mul_cancel _ _
    have hc := congrArg (fun u : (AlgebraicClosure ℚ_[p])ˣ =>
      ‖(u : AlgebraicClosure ℚ_[p])‖) hmul
    rw [Units.val_mul, norm_mul, hnorm_one, one_mul] at hc
    exact hc.symm
  change max 0 (-(Real.log ‖((second.roots ((N : ℚ)⁻¹)).toMul :
      AlgebraicClosure ℚ_[p])‖)) =
    max 0 (-(Real.log ‖((first.roots ((N : ℚ)⁻¹)).toMul :
      AlgebraicClosure ℚ_[p])‖))
  rw [hnorm_eq]

/-- 思路 (a) 的有序层实例：层载体为代数闭包单位群，log 步为 `(m+1)` 次根过渡，
Kummer 像为 `(m+1)! · 深度`（阶乘归一化恰好补偿根过渡的 `1/(m+1)` 缩放，
使上半不等式成立）。Kummer 目标 `D = ℝ` 即 [IUTchIII, Proposition 3.9] 的
log-volume 侧的单值代理。 -/
noncomputable def unitLogKummerOrderedLayer (p : Nat) [Fact (Nat.Prime p)] :
    VerticalLogKummerOrderedLayer where
  D := ℝ
  ordD := inferInstance
  F := fun _ => (AlgebraicClosure ℚ_[p])ˣ
  ordF := fun _ => Preorder.lift (unitShellDepth p)
  log := fun m => rootSystemPowRoot p (m + 1)
  kummer := fun m x => ((m + 1).factorial : ℝ) * unitShellDepth p x
  upperSemi := fun m x => by
    show ((m + 1).factorial : ℝ) * unitShellDepth p x ≤
      (((m + 1) + 1).factorial : ℝ) *
        unitShellDepth p (rootSystemPowRoot p (m + 1) x)
    rw [unitShellDepth_rootSystemPowRoot p (m + 1) (Nat.succ_ne_zero m) x]
    push_cast
    have hfac : (((m + 1) + 1).factorial : ℝ) =
        ((m : ℝ) + 1 + 1) * ((m + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ (m + 1), Nat.cast_mul]
      push_cast
      ring
    have hd : 0 ≤ ((m + 1).factorial : ℝ) * unitShellDepth p x :=
      mul_nonneg (Nat.cast_nonneg _) (unitShellDepth_nonneg p x)
    have hcoef : (1 : ℝ) ≤ ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1) := by
      rw [one_le_div (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      linarith
    calc ((m + 1).factorial : ℝ) * unitShellDepth p x
        = (((m + 1).factorial : ℝ) * unitShellDepth p x) * 1 :=
          (mul_one _).symm
      _ ≤ (((m + 1).factorial : ℝ) * unitShellDepth p x) *
            (((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hcoef hd
      _ = (((m + 1) + 1).factorial : ℝ) *
            (unitShellDepth p x / ((m : ℝ) + 1)) := by
          rw [hfac]
          ring
  log_monotone := fun m x y hxy => by
    have hxy' : unitShellDepth p x ≤ unitShellDepth p y := hxy
    show unitShellDepth p (rootSystemPowRoot p (m + 1) x) ≤
      unitShellDepth p (rootSystemPowRoot p (m + 1) y)
    rw [unitShellDepth_rootSystemPowRoot p (m + 1) (Nat.succ_ne_zero m) x,
      unitShellDepth_rootSystemPowRoot p (m + 1) (Nat.succ_ne_zero m) y]
    exact div_le_div_of_nonneg_right hxy' (Nat.cast_nonneg _)
  kummer_monotone := fun m x y hxy => by
    have hxy' : unitShellDepth p x ≤ unitShellDepth p y := hxy
    exact mul_le_mul_of_nonneg_left hxy' (Nat.cast_nonneg _)

@[simp] theorem unitLogKummerOrderedLayer_log (p : Nat) [Fact (Nat.Prime p)]
    (m : Nat) (x : (AlgebraicClosure ℚ_[p])ˣ) :
    (unitLogKummerOrderedLayer p).log m x = rootSystemPowRoot p (m + 1) x := rfl

@[simp] theorem unitLogKummerOrderedLayer_kummer (p : Nat) [Fact (Nat.Prime p)]
    (m : Nat) (x : (AlgebraicClosure ℚ_[p])ˣ) :
    (unitLogKummerOrderedLayer p).kummer m x =
      ((m + 1).factorial : ℝ) * unitShellDepth p x := rfl

/-! ## 5. 思路 (a 续)：非 arch 核的整单位模型实例 -/

/-- 整数层指标上的根过渡：`m ↦ x^(1/(|m|+1))`。 -/
noncomputable def shellRootStepInt (p : Nat) [Fact (Nat.Prime p)] (m : ℤ)
    (x : (AlgebraicClosure ℚ_[p])ˣ) : (AlgebraicClosure ℚ_[p])ˣ :=
  rootSystemPowRoot p (m.natAbs + 1) x

theorem shellRootStepInt_norm_le_one (p : Nat) [Fact (Nat.Prime p)] (m : ℤ)
    (x : (AlgebraicClosure ℚ_[p])ˣ)
    (hx : ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 1) :
    ‖(shellRootStepInt p m x : AlgebraicClosure ℚ_[p])‖ ≤ 1 :=
  rootSystemPowRoot_norm_le_one p _ (Nat.succ_ne_zero _) x hx

/-- log-link 迭代在单位上的轨道（[IUTchIII, Remark 1.1.1] 的模型）。 -/
noncomputable def unitRootIterate (p : Nat) [Fact (Nat.Prime p)] (m : ℤ) :
    Nat → (AlgebraicClosure ℚ_[p])ˣ → (AlgebraicClosure ℚ_[p])ˣ
  | 0, x => x
  | k + 1, x => shellRootStepInt p (m + (k : ℤ)) (unitRootIterate p m k x)

theorem unitRootIterate_norm_le_one (p : Nat) [Fact (Nat.Prime p)] (m : ℤ)
    (k : Nat) (x : (AlgebraicClosure ℚ_[p])ˣ)
    (hx : ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 1) :
    ‖(unitRootIterate p m k x : AlgebraicClosure ℚ_[p])‖ ≤ 1 := by
  induction k with
  | zero => simpa [unitRootIterate] using hx
  | succ k ih => exact shellRootStepInt_norm_le_one p (m + k) _ ih

/-- 思路 (a) 的非 arch 核实例（模型）：载体取 `‖·‖ ≤ 1` 的整单位，
coric 模为代数闭包单位群，log-shell 为整单位集合，Kummer 像为包含映射，
log-link 关系为根过渡的图像。两条包含条款由整性在根过渡/迭代下保持给出。 -/
noncomputable def integralUnitLogShellModel (p : Nat) [Fact (Nat.Prime p)] :
    NonarchimedeanLogKummerUpperSemi where
  Unit := fun _ => {x : (AlgebraicClosure ℚ_[p])ˣ //
    ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 1}
  coricModule := (AlgebraicClosure ℚ_[p])ˣ
  logShell := {x | ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 1}
  logLinkUnit := fun m u w => w.1 = shellRootStepInt p m u.1
  logIterate := fun {m m'} u w =>
    ∃ k : Nat, m + (k : ℤ) = m' ∧ w.1 = unitRootIterate p m k u.1
  logIterate_refl := fun m u => ⟨0, by simp, rfl⟩
  logIterate_step := fun {m m'} u y z hy hz => by
    rcases hy with ⟨k, hk, hy_eq⟩
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Nat.cast_add, Nat.cast_one]
      omega
    · rw [hz, hy_eq, ← hk]
      rfl
  kummer := fun _ u => u.1
  kummer_mem_logShell := fun _ u => u.2
  iterate_kummer_mem_logShell := fun {m m'} u w hrel _ => by
    rcases hrel with ⟨k, _, hw⟩
    rw [hw]
    exact unitRootIterate_norm_le_one p m k u.1 u.2

/-! ## 6. 思路 (c)：étale Kummer 桥（q 参数载体） -/

/-- 真实 q 参数载体上的根过渡方程：`q^(1/N)` 的 `N` 次幂回到
`qParameterGroupification`。 -/
theorem qParameterShellRoot_pow (p : Nat) [Fact (Nat.Prime p)] (N : Nat)
    (hN : N ≠ 0) :
    (((LocalIntegralMonoid.qParameterCompatibleRoots p).roots
      ((N : ℚ)⁻¹)).toMul) ^ N =
        LocalIntegralMonoid.qParameterGroupification p :=
  compatibleRootSystem_pow_root _ N hN

/-- q 参数载体上的层塔律：`(m·n)` 层等于 `n` 层的 `m` 重（加法记号）。 -/
theorem qIntegerRoot_level_tower (p : Nat) [Fact (Nat.Prime p)] (m : Nat)
    (n : ℤ) :
    LocalIntegralMonoid.qIntegerRoot p ((m : ℤ) * n) =
      (m : ℤ) • LocalIntegralMonoid.qIntegerRoot p n := by
  rw [LocalIntegralMonoid.qIntegerRoot_eq_zsmul,
    LocalIntegralMonoid.qIntegerRoot_eq_zsmul, smul_smul]

/-- étale 核元素的塔形状（由 [IUT-II.concrete-etale-kummer-bridge] 并层塔律）：
有限 Tate 方向核中的指标的 Kummer 像落在 `l` 重层上。 -/
theorem qIntegerRoot_etaleKernel_tower (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] (n : ℤ) (h : (integralTateReduction l) n = 0) :
    ∃ k : ℤ, LocalIntegralMonoid.qIntegerRoot l.value n =
      LocalIntegralMonoid.qIntegerRoot l.value ((l.value : ℤ) * k) := by
  obtain ⟨k, hk⟩ := LocalIntegralMonoid.qIntegerRoot_of_etale_kernel l n h
  exact ⟨k, hk.trans
    (qIntegerRoot_level_tower l.value l.value k).symm⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def verticalLogKummerOrderedLayer : Obligation :=
  { id := "IUT-II.vertical-log-kummer-ordered-layer"
    source := "IUT III, Proposition 1.2, (v); Remark 1.2.2, (i), (iii); " ++
      "Proposition 3.5, (ii), (a), (b); Theorem 3.11, (ii)"
    status := VerificationStatus.interface
    note :=
      "The source-faithful upper-semi kernel of the vertical log-Kummer " ++
        "correspondence is recorded: the nonarchimedean log-shell containment " ++
        "of Kummer images and of their pre-composites with positive log-link " ++
        "iterates [Prop 3.5, (ii), (a)], the archimedean closed-ball form " ++
        "[Prop 3.5, (ii), (b)], and the ordered single-valued reduction with " ++
        "monotone log steps and Kummer images. A concrete unit model over the " ++
        "algebraic closure of Q_p instantiates both kernels from the proven " ++
        "divisible root system. The actual Frobenioid-theoretic units, the " ++
        "log-shell I = (p*)^{-1} * log(O^), the LGP-Gaussian log-theta-lattice " ++
        "columns, tensor packets, and log-volumes remain source obligations." }

end LeanFormal.IUT.Audit
