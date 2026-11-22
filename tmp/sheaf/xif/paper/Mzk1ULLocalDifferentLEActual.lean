/-
# Mzk1UL：different 的局部化 ≤ 方向（differentLocalizationLEObligation）的弱化版

消费者：donor Mzk1ULLocalizationObligationsActual.differentLocalizationLEObligation
（Ideal.map (algebraMap B Bq) (differentIdeal A B) ≤ differentIdeal Ap Bq），
以及它的下游 map_differentIdeal_le_of_obligation（david 的 per-place 界只用 ≤ 方向）。
本文件不改任何 donor 文件、不改义务的 Prop 定义，只给出**可证的部分**与**精确残差**。

## 1. 精确残差（未证部分，如实记录）

设 A = 𝓞 F、B = 𝓞 L、Ap = Localization.AtPrime p、Bq = Localization.AtPrime Q，
p = Q.under A。要证 map 𝔇_{B/A} ≤ 𝔇_{Bq/Ap}。等价的元素级内容（本文件用
Submodule.traceDual 精确写出来，见下面的 _of_traceDual 定理）是：

  **残差 R1（codifferent 的乘法条件）**：对局部 codifferent
  D' := Submodule.traceDual Ap (FractionRing Ap) (1 : Submodule Bq (FractionRing Bq))
  的每个 w，以及每个 y ∈ 𝔇_{B/A}，都有
  w * algebraMap Bq (FractionRing Bq) (algebraMap B Bq y) ∈ (1 : Submodule Bq _)。

  **残差 R2（局部 different 的 trace 判据）**：∀ y : Bq，若 y 与 D' 的乘法落在 1 中，
  则 y ∈ 𝔇_{Bq/Ap}。

R2 在「局部 AKLB 正规化」下就是 TauCetiPort 的源码引理
TauCeti.mem_differentIdeal_iff_forall_mem_traceDual
（tmp/sheaf/xif/paper/TauCetiPort/TauCeti/RingTheory/DedekindDomain/Different/Basic.lean:109），
把 (R, S, K, L) 取成 (Ap, Bq, FractionRing Ap, FractionRing Bq) 即可。
但这条路线本文件**不能直接用**（已实测，见下），故 R2 作为显式参数：
  * 该文件的上下文要求 IsIntegralClosure Bq Ap (FractionRing Bq)、FiniteDimensional、
    Algebra.IsSeparable，而 donor 义务的 binder 里没有这些；
  * 更硬的问题是 TauCetiPort 的该文件在当前 Mathlib 里**编译不过**（watchdog 记录
    FAIL，三个错误：第 98/279 行 NeZero 1 合成失败、第 190 行未知标识符
    not_dvd_differentIdeal_of_intTrace_notMem），因此无法 import 其 olean（不存在）。
    要复用它，需先修 TauCetiPort（另一任务），本文件不碰他人文件。

R1 才是 Mathlib 4.32.2 真正缺的引理：Submodule.traceDual 沿 B → Bq 的局部化
=R1（配 Algebra.trace_localization，Mathlib/RingTheory/Localization/NormTrace.lean:84，
它需要 [Module.Free R S] [Module.Finite R S]，对 (A, B) 成立）。注意 R1 的
「trace-dual → different」搬运用的是 Submodule.traceDual 的**乘法**判据
（1 / D 的元素刻画 Submodule.mem_div_iff_forall_mul_mem，
见 Different.lean:475 的 differentIdeal 定义与 TauCeti 上述引理的证明），
故 R1 是 map ≤ map 的唯一实质内容。

## 2. 一个必须记录的负面发现：Lead 提示的「朴素 trace 判据」是错的

x ∈ 𝔇_{B/A} ⟺ ∀ y : B, Algebra.trace (x * y) ∈ A **不成立**：满足右式的元素
是 codifferent 𝔇⁻¹ = Submodule.traceDual A (FractionRing A) 1（元素在 FractionRing 里，
不必在 B 中），而 𝔇 = (𝔇⁻¹)⁻¹ 需要再取一次逆（x ∈ 𝔇 ⟺ x ∈ B 且 x·(𝔇⁻¹) ⊆ B）。
反例：A = ℤ, B = ℤ[√2]（disc = 8, 𝔇 = (2, √2)）；取 x = 1，对每个 y = a + b√2 ∈ B 有
Tr(y) = 2a ∈ ℤ，但 1 ∉ 𝔇。所以本文件一律用 Submodule.traceDual + 1 / -（codifferent
取逆）的写法，不用朴素 trace 判据。这一步也解释了为什么 donor 的「精确缺件」写的是
trace-dual 的局部化，而不是 Algebra.trace_localization 本身。

## 3. 本文件证了什么

* differentLocalizationLEObligation_of_differentIdeal_eq_top：局部 different 平凡时成立
  （例如 Q = ⊥ 的泛点纤维，或该位非分歧且其余位已处理时；𝔇 = ⊤ 是确切假设）。
* differentLocalizationLEObligation_of_differentIdeal_eq_bot：𝔇_{B/A} = ⊥ 时成立。
* differentLocalizationLEObligation_of_comap_eq：donor 义务的**更强形式**
  (differentIdeal Ap Bq).comap (algebraMap B Bq) = differentIdeal A B 蕴含 ≤ 方向。
* differentLocalizationLEObligation_of_traceDual：**主定理**，把 ≤ 方向精确归约到
  R1 + R2（两者都是显式、可验证的假设；结论仍是原样的 ≤，没有改目标）。
（R2 若由修好的 TauCetiPort 引理提供，则残差收缩为唯一的 R1；本文件因该 port 编译不过
而没有引入它，见 §1 末尾。）
-/
import tmp.sheaf.xif.paper.Mzk1ULLocalizationObligationsActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentLEActual

open LeanFormal.IUT.XiFPaper.Mzk1ULLocalizationObligationsActual

/-- 与 donor 义务完全相同的 binder（一字不改，便于直接 instance/prove）。 -/
section DifferentLocalizationLE

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable {Ap : Type*} [CommRing Ap] [IsDomain Ap] [IsIntegrallyClosed Ap] [Algebra A Ap]
variable {Bq : Type*} [CommRing Bq] [IsDomain Bq] [IsDedekindDomain Bq] [Algebra B Bq]
  [Algebra Ap Bq] [Module.IsTorsionFree Ap Bq]

/-- **弱化版 1**：局部 different 平凡（𝔇_{Bq/Ap} = ⊤）时 ≤ 方向自动成立。 -/
theorem differentLocalizationLEObligation_of_differentIdeal_eq_top
    (h : differentIdeal Ap Bq = ⊤) :
    differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) := by
  unfold differentLocalizationLEObligation
  rw [h]
  exact le_top

/-- **弱化版 2**：𝔇_{B/A} = ⊥ 时 ≤ 方向成立（左侧为 ⊥）。 -/
theorem differentLocalizationLEObligation_of_differentIdeal_eq_bot
    (h : differentIdeal A B = ⊥) :
    differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) := by
  unfold differentLocalizationLEObligation
  rw [h, Ideal.map_bot]
  exact bot_le

/-- **弱化版 3（更强的等式义务 ⟹ ≤）**：若沿 algebraMap B Bq 的 comap 恰好给出
全局 different（即「different 的局部化」的强形式），则 ≤ 方向成立。
这是 differentLocalizationLEObligation 的一个严格更强的充分条件。 -/
theorem differentLocalizationLEObligation_of_comap_eq
    (h : (differentIdeal Ap Bq).comap (algebraMap B Bq) = differentIdeal A B) :
    differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) := by
  unfold differentLocalizationLEObligation
  rw [Ideal.map_le_iff_le_comap, h]
  exact le_rfl

/-- **主定理（精确归约）**：≤ 方向由两个显式、可验证的假设推出，结论保持原样。

* hcrit（残差 R2，局部的 trace 判据）：与局部 codifferent
  D' = Submodule.traceDual Ap (FractionRing Ap) 1 的乘法落在 1 中的元素属于
  𝔇_{Bq/Ap}。在局部 AKLB 正规化下它就是 TauCetiPort 的
  TauCeti.mem_differentIdeal_iff_forall_mem_traceDual。
* htrace（残差 R1，codifferent 的局部化/乘法条件）：D' 的每个元素把
  𝔇_{B/A} 在 Bq 中的像乘进 1。这是 Mathlib 缺的 trace-dual 局部化引理的
  元素级形式（由 Algebra.trace_localization 提供实质内容）。

不新增 axiom、不用 sorry；两个假设都是对 Submodule.traceDual / differentIdeal
的可判定陈述，消费者可分别攻。 -/
theorem differentLocalizationLEObligation_of_traceDual
    (hcrit : ∀ y : Bq,
      (∀ w ∈ Submodule.traceDual Ap (FractionRing Ap) (1 : Submodule Bq (FractionRing Bq)),
          w * algebraMap Bq (FractionRing Bq) y ∈ (1 : Submodule Bq (FractionRing Bq))) →
        y ∈ differentIdeal Ap Bq)
    (htrace : ∀ w ∈ Submodule.traceDual Ap (FractionRing Ap) (1 : Submodule Bq (FractionRing Bq)),
        ∀ y : B, y ∈ differentIdeal A B →
          w * algebraMap Bq (FractionRing Bq) (algebraMap B Bq y) ∈
            (1 : Submodule Bq (FractionRing Bq))) :
    differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) := by
  unfold differentLocalizationLEObligation
  rw [Ideal.map_le_iff_le_comap]
  intro y hy
  exact hcrit _ (fun w hw => htrace w hw y hy)

end DifferentLocalizationLE

#print axioms differentLocalizationLEObligation_of_differentIdeal_eq_top
#print axioms differentLocalizationLEObligation_of_differentIdeal_eq_bot
#print axioms differentLocalizationLEObligation_of_comap_eq
#print axioms differentLocalizationLEObligation_of_traceDual

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentLEActual
