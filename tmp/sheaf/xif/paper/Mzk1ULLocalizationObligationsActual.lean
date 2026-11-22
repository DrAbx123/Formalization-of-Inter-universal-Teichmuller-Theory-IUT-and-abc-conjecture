/-
# Mzk1UL 局部化义务：fiberInertiaBridge 关闭 + differentLocalizationObligation 的精确 ≤/≥ 拆分

本文件只处理两个**具名局部化义务**（不与任何其它文件冲突；消费者为 david 的 per-vQ
局部对象 / per-place 界）：

* **义务 2（fiberInertiaBridge，donor Mzk1ULLocalConductorizationActual）已关闭**：
  取 floc := fun P => (P.asIdeal).inertiaDeg ℤ 时义务是 rfl（定义展开后左右同一项）。
  由此 donor 的条件版装配 localConductor_eq_global_of_bridge 变成无条件定理
  localConductor_eq_global_self。同一有理素数 fiber 内的求和恒等
  ∑ f_P·log p = (∑ f_P)·log p 是 Finset.sum_mul（rfl 级）。
  另给出 fiberInertiaBridge_iff 作为该义务的精确展开。

* **义务 1（differentLocalizationObligation，donor Mzk1ULLocalDifferentizationActual）
  拆成两个精确的残差义务**：
  differentLocalizationLEObligation（≤ 方向，david 的 per-place 界只消费这一半）
  与 differentLocalizationGEObligation（≥ 方向）。二者合起来恰好是原等式义务
  （differentLocalizationObligation_iff_le_and_ge，le_antisymm_iff）。

## 义务 1 的精确缺件（Mathlib 4.32.2，rev 905b95818eb32af7874a58b427f50c1711a5e96c）

在典型情形 A = 𝓞 F、B = 𝓞 L、Ap = Localization.AtPrime p、
Bq = Localization.AtPrime Q（p = Q.under A）下，等式两侧都由
differentIdeal 的 trace-dual 定义给出：

* Mathlib/RingTheory/DedekindDomain/Different.lean:474
  differentIdeal A B = (1 / Submodule.traceDual A (FractionRing A) 1).comap ...；
* 局部化侧是同一个构造，只是把 A 换成 Ap（FractionRing Ap ≅ FractionRing A），
  并把 FractionRing B 上的 B-子模局部化到 Bq。

因此 ≤ 方向需要的**唯一**缺失引理是 trace-dual 与局部化的交换：

  (Submodule.traceDual A (FractionRing A) 1) 沿 B → Bq 的局部化
    = Submodule.traceDual Ap (FractionRing Ap) 1（在 FractionRing B 内），

再由 1 / - 反序即得 differentLocalizationLEObligation；≥ 方向需要同一等式的
反向包含（即该 trace-dual 局部化等式的 ≥ 半）。Mathlib 现状：
* 有逐元素的 Algebra.trace_localization
  （Mathlib/RingTheory/Localization/NormTrace.lean:84，条件 [Module.Free R S] [Module.Finite R S]），
  但**没有** Submodule.traceDual / BilinForm.dualSubmodule 的局部化版本；
* 有 Submodule.localized'（Mathlib/Algebra/Module/LocalizedModule/Submodule.lean）
  与 Ideal.localized'_eq_map，但**没有** FractionalIdeal.dual 与
  FractionalIdeal.extendedHom 的交换律；
* differentIdeal_eq_differentIdeal_mul_differentIdeal 需要 Module.Finite B C，
  对 C = Bq（局部化）**不成立**，不能用来绕过该缺件。

故本文件如实保留 differentLocalizationLEObligation / differentLocalizationGEObligation
为显式义务（不新增 axiom、不用 sorry），并额外证明它们在平凡局部化 Ap = A, Bq = B
下成立（非空性检查），以及原义务与两半的精确等价。
-/
import tmp.sheaf.xif.paper.Mzk1ULLocalDifferentizationActual
import tmp.sheaf.xif.paper.Mzk1ULLocalConductorizationActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalizationObligationsActual

open NumberField IsDedekindDomain
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorizationActual
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual
open LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

/-! ### 义务 2：fiberInertiaBridge（已关闭） -/

variable {K : Type*} [Field K] [NumberField K]

/-- **义务 2 关闭**：取局部剩余次数 floc P := (P.asIdeal).inertiaDeg ℤ 时
fiberInertiaBridge 成立（rfl：定义展开后左右是同一项，不涉及完成域桥）。

消费：donor localConductor_eq_global_of_bridge 的条件版由此变为无条件版
localConductor_eq_global_self。 -/
theorem fiberInertiaBridge_self :
    fiberInertiaBridge (K := K) (fun P : HeightOneSpectrum (𝓞 K) =>
      (P.asIdeal).inertiaDeg ℤ) :=
  fun _ => rfl

/-- fiberInertiaBridge 的精确展开（定义即 ∀ P, floc P = ...）。 -/
theorem fiberInertiaBridge_iff (floc : HeightOneSpectrum (𝓞 K) → ℕ) :
    fiberInertiaBridge (K := K) floc ↔
      ∀ P : HeightOneSpectrum (𝓞 K), floc P = (P.asIdeal).inertiaDeg ℤ :=
  Iff.rfl

/-- **fiber 求和恒等**（真题要求的形式）：同一有理素数 p 的 fiber 内，
f_P · log p 之和 = (∑ f_P) · log p。这里 f_P = inertiaDeg ℤ；
证明只是 Finset.sum_mul（rfl 级，不需要完成域桥）。 -/
theorem fiber_sum_inertiaDeg_mul_log_eq
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        (((P.asIdeal).inertiaDeg ℤ : ℝ) * Real.log (p : ℝ))) =
      (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        (((P.asIdeal).inertiaDeg ℤ : ℝ))) * Real.log (p : ℝ) := by
  rw [Finset.sum_mul]

/-- 对任意 floc 的同一求和恒等（纯 Finset.sum_mul）。 -/
theorem fiber_sum_mul_log_eq (floc : HeightOneSpectrum (𝓞 K) → ℕ)
    (bad : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        ((floc P : ℝ) * Real.log (p : ℝ))) =
      (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        (floc P : ℝ)) * Real.log (p : ℝ) := by
  rw [Finset.sum_mul]

/-- **david 的逐位装配，无条件版**：f_P = inertiaDeg ℤ 的逐位和
= [K:ℚ] · logConductorDeg K bad（donor localConductor_eq_global_of_bridge
在 fiberInertiaBridge_self 上的特例）。 -/
theorem localConductor_eq_global_self
    (bad : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑ P ∈ bad, (((P.asIdeal).inertiaDeg ℤ : ℝ) *
        Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ))) =
      (Module.finrank ℚ K : ℝ) * logConductorDeg K bad :=
  localConductor_eq_global_of_bridge (K := K)
    (floc := fun P : HeightOneSpectrum (𝓞 K) => (P.asIdeal).inertiaDeg ℤ)
    (fiberInertiaBridge_self (K := K)) bad

/-! ### 义务 1：differentLocalizationObligation 的精确 ≤/≥ 拆分 -/

section DifferentLocalization

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable {Ap : Type*} [CommRing Ap] [IsDomain Ap] [IsIntegrallyClosed Ap] [Algebra A Ap]
variable {Bq : Type*} [CommRing Bq] [IsDomain Bq] [IsDedekindDomain Bq] [Algebra B Bq]
  [Algebra Ap Bq] [Module.IsTorsionFree Ap Bq]

/-- **残差义务（≤ 方向，精确陈述）**：
𝔇_{B/A} 在 Bq 处的扩张包含于局部 different 𝔇_{Bq/Ap}。

典型情形 Ap = Localization.AtPrime p、Bq = Localization.AtPrime Q
（p = Q.under A）。david 的 per-place 局部界只需要这一半（见 donor
map_differentIdeal_le_of_obligation 的用法）。

精确缺件（Mathlib 4.32.2 无）：Submodule.traceDual 沿 B → Bq 的局部化
等于 Bq/Ap 的 trace dual；对 1 / - 反序即得本不等式。详见文件头。 -/
def differentLocalizationLEObligation : Prop :=
  Ideal.map (algebraMap B Bq) (differentIdeal A B) ≤ differentIdeal Ap Bq

/-- **残差义务（≥ 方向，精确陈述）**：
局部 different 𝔇_{Bq/Ap} 包含于 𝔇_{B/A} 的扩张。

与 ≤ 方向合起来才给出 donor 的等式义务。精确缺件：trace-dual 局部化等式的
反向包含（同上，Mathlib 4.32.2 无 Submodule.traceDual 的局部化引理）。 -/
def differentLocalizationGEObligation : Prop :=
  differentIdeal Ap Bq ≤ Ideal.map (algebraMap B Bq) (differentIdeal A B)

/-- **精确拆分**：donor 的等式义务 ↔ ≤ 方向 ∧ ≥ 方向（le_antisymm_iff）。 -/
theorem differentLocalizationObligation_iff_le_and_ge :
    differentLocalizationObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) ↔
      differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) ∧
        differentLocalizationGEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) := by
  unfold differentLocalizationObligation differentLocalizationLEObligation
    differentLocalizationGEObligation
  exact le_antisymm_iff

/-- 由等式义务得到 ≤ 方向（供 david 的 per-place 界消费）。 -/
theorem differentLocalizationLE_of_obligation
    (h : differentLocalizationObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq)) :
    differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) :=
  ((differentLocalizationObligation_iff_le_and_ge (A := A) (B := B) (Ap := Ap)
    (Bq := Bq)).mp h).1

/-- 由等式义务得到 ≥ 方向。 -/
theorem differentLocalizationGE_of_obligation
    (h : differentLocalizationObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq)) :
    differentLocalizationGEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) :=
  ((differentLocalizationObligation_iff_le_and_ge (A := A) (B := B) (Ap := Ap)
    (Bq := Bq)).mp h).2

/-- 由 ≤ 与 ≥ 两个方向合出等式义务（供两条独立路线分别攻残差时装配）。 -/
theorem differentLocalizationObligation_of_le_of_ge
    (hle : differentLocalizationLEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq))
    (hge : differentLocalizationGEObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq)) :
    differentLocalizationObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq) :=
  (differentLocalizationObligation_iff_le_and_ge (A := A) (B := B) (Ap := Ap)
    (Bq := Bq)).mpr ⟨hle, hge⟩

/-- 非空性检查：平凡局部化 Ap = A、Bq = B 时 ≤ 方向成立。 -/
theorem differentLocalizationLEObligation_self :
    differentLocalizationLEObligation (A := A) (B := B) (Ap := A) (Bq := B) := by
  unfold differentLocalizationLEObligation
  simp

/-- 非空性检查：平凡局部化时 ≥ 方向成立。 -/
theorem differentLocalizationGEObligation_self :
    differentLocalizationGEObligation (A := A) (B := B) (Ap := A) (Bq := B) := by
  unfold differentLocalizationGEObligation
  simp

/-- 非空性检查：平凡局部化时 donor 的等式义务成立。 -/
theorem differentLocalizationObligation_self :
    differentLocalizationObligation (A := A) (B := B) (Ap := A) (Bq := B) :=
  differentLocalizationObligation_of_le_of_ge
    (A := A) (B := B) (Ap := A) (Bq := B)
    differentLocalizationLEObligation_self differentLocalizationGEObligation_self

end DifferentLocalization

#print axioms fiberInertiaBridge_self
#print axioms fiberInertiaBridge_iff
#print axioms fiber_sum_inertiaDeg_mul_log_eq
#print axioms fiber_sum_mul_log_eq
#print axioms localConductor_eq_global_self
#print axioms differentLocalizationLEObligation
#print axioms differentLocalizationGEObligation
#print axioms differentLocalizationObligation_iff_le_and_ge
#print axioms differentLocalizationLE_of_obligation
#print axioms differentLocalizationGE_of_obligation
#print axioms differentLocalizationObligation_of_le_of_ge
#print axioms differentLocalizationLEObligation_self
#print axioms differentLocalizationGEObligation_self
#print axioms differentLocalizationObligation_self

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalizationObligationsActual
