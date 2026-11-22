/- G1-A：Fermat 曲线图环 / 局部模型的 x↔y 对换（对称性基础设施）。
   F = X0^n + X1^n - 1 对称，故 R n 有 x↔y 的 Q-代数自同构；
   局部模型 Model = Q[x,y,z]/(F, (n x^{n-1}) z - 1) 对换到 y-侧模型
   Model_swap = Q[x,y,z]/(F, (n y^{n-1}) z - 1)。
   用途：把 r-侧的 standard smooth / localization 结果运输到 r' = n y^{n-1} 侧，
   避免整份复制 SmoothAttempt / SmoothLocalize。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatSmoothAttemptActual
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSwapActual
open Polynomial MvPolynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothAttemptActual

abbrev A2 : Type := MvPolynomial (Fin 2) ℚ
abbrev A3 : Type := MvPolynomial (Fin 3) ℚ

/-- 2 变量对换。 -/
def swap2 : Equiv (Fin 2) (Fin 2) := Equiv.swap 0 1
/-- 3 变量对换（0↔1，2 固定）。 -/
def swap3 : Equiv (Fin 3) (Fin 3) := Equiv.swap 0 1

@[simp] theorem swap2_zero : swap2 0 = 1 := by decide
@[simp] theorem swap2_one : swap2 1 = 0 := by decide
@[simp] theorem swap3_zero : swap3 0 = 1 := by decide
@[simp] theorem swap3_one : swap3 1 = 0 := by decide
@[simp] theorem swap3_two : swap3 2 = 2 := by decide

/-- 2 变量环的交换代数等价。 -/
noncomputable def swapA2 : A2 ≃ₐ[ℚ] A2 := MvPolynomial.renameEquiv ℚ swap2

theorem swapA2_fermatEquation (n : Nat) :
    swapA2 (fermatEquation n) = fermatEquation n := by
  simp only [swapA2, MvPolynomial.renameEquiv_apply, fermatEquation, map_sub, map_add,
    map_pow, map_one, MvPolynomial.rename_X, swap2_zero, swap2_one]
  ring

theorem image_fermatEquation_under_swap (n : Nat) :
    (swapA2 : A2 → A2) '' ({fermatEquation n} : Set A2) = {fermatEquation n} := by
  ext x
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hy]
    exact swapA2_fermatEquation n
  · intro hx
    exact ⟨fermatEquation n, rfl, by rw [hx, swapA2_fermatEquation]⟩

theorem map_span_fermatEquation (n : Nat) :
    (Ideal.span {fermatEquation n}).map (swapA2 : A2 →+* A2) = Ideal.span {fermatEquation n} := by
  rw [Ideal.map_span]
  change Ideal.span ((swapA2 : A2 → A2) '' ({fermatEquation n} : Set A2))
    = Ideal.span {fermatEquation n}
  rw [image_fermatEquation_under_swap]

/-- R n 的 x↔y 自同构。 -/
noncomputable def swapR (n : Nat) : R n ≃ₐ[ℚ] R n :=
  Ideal.quotientEquivAlg (Ideal.span {fermatEquation n}) (Ideal.span {fermatEquation n}) swapA2 (by
    show Ideal.span {fermatEquation n}
      = (Ideal.span {fermatEquation n}).map (swapA2 : A2 →+* A2)
    rw [map_span_fermatEquation])

/-- y-侧局部化模型的关系：F 与 (n y^{n-1}) z - 1。 -/
def modelSwapRel (n : Nat) (i : Fin 2) : MvPolynomial (Fin 3) ℚ :=
  if i = 0 then MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1
  else ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 1 ^ (n - 1)) *
    MvPolynomial.X 2 - 1

theorem modelSwapRel_zero (n : Nat) :
    modelSwapRel n 0 = MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1 := by
  simp [modelSwapRel]

theorem modelSwapRel_one (n : Nat) :
    modelSwapRel n 1 = ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 1 ^ (n - 1)) *
      MvPolynomial.X 2 - 1 := by
  simp [modelSwapRel]

/-- y-侧局部化模型环。 -/
noncomputable abbrev ModelSwap (n : Nat) : Type :=
  MvPolynomial (Fin 3) ℚ ⧸ Ideal.span (Set.range (modelSwapRel n))

#print axioms swapA2_fermatEquation
#print axioms map_span_fermatEquation
#print axioms swapR
/-- 3 变量环的交换代数等价。 -/
noncomputable def swapA3 : A3 ≃ₐ[ℚ] A3 := MvPolynomial.renameEquiv ℚ swap3

/-- r-侧模型环的别名。 -/
noncomputable abbrev Model (n : Nat) : Type := fermatModelRing n

theorem swapA3_modelSwapRel_zero (n : Nat) :
    swapA3 (modelSwapRel n 0) = fermatModelRel n 0 := by
  rw [modelSwapRel_zero, fermatModelRel_zero]
  simp only [swapA3, MvPolynomial.renameEquiv_apply, map_sub, map_add, map_pow, map_one,
    MvPolynomial.rename_X, swap3_zero, swap3_one]
  ring

theorem swapA3_modelSwapRel_one (n : Nat) :
    swapA3 (modelSwapRel n 1) = fermatModelRel n 1 := by
  rw [modelSwapRel_one, fermatModelRel_one, swapA3, MvPolynomial.renameEquiv_apply]
  simp only [map_sub, map_mul, map_pow, map_one, map_natCast, MvPolynomial.rename_X,
    swap3_zero, swap3_one, swap3_two]

theorem swapA3_fermatModelRel_zero (n : Nat) :
    swapA3 (fermatModelRel n 0) = modelSwapRel n 0 := by
  rw [fermatModelRel_zero, modelSwapRel_zero]
  simp only [swapA3, MvPolynomial.renameEquiv_apply, map_sub, map_add, map_pow, map_one,
    MvPolynomial.rename_X, swap3_zero, swap3_one]
  ring

theorem swapA3_fermatModelRel_one (n : Nat) :
    swapA3 (fermatModelRel n 1) = modelSwapRel n 1 := by
  rw [fermatModelRel_one, modelSwapRel_one, swapA3, MvPolynomial.renameEquiv_apply]
  simp only [map_sub, map_mul, map_pow, map_one, map_natCast, MvPolynomial.rename_X,
    swap3_zero, swap3_one, swap3_two]

theorem image_fermatModelRel_under_swap (n : Nat) :
    (swapA3 : A3 → A3) '' Set.range (fermatModelRel n) = Set.range (modelSwapRel n) := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact ⟨0, (swapA3_fermatModelRel_zero n).symm⟩
    · exact ⟨1, (swapA3_fermatModelRel_one n).symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨fermatModelRel n 0, ⟨0, rfl⟩, swapA3_fermatModelRel_zero n⟩
    · exact ⟨fermatModelRel n 1, ⟨1, rfl⟩, swapA3_fermatModelRel_one n⟩

theorem map_span_fermatModelRel (n : Nat) :
    (Ideal.span (Set.range (fermatModelRel n))).map (swapA3 : A3 →+* A3)
      = Ideal.span (Set.range (modelSwapRel n)) := by
  rw [Ideal.map_span]
  change Ideal.span ((swapA3 : A3 → A3) '' Set.range (fermatModelRel n))
    = Ideal.span (Set.range (modelSwapRel n))
  rw [image_fermatModelRel_under_swap]

/-- **r-侧模型 ≃ y-侧模型**（x↔y 对换）。 -/
noncomputable def ModelSwapEquiv (n : Nat) : Model n ≃ₐ[ℚ] ModelSwap n :=
  Ideal.quotientEquivAlg (Ideal.span (Set.range (fermatModelRel n)))
    (Ideal.span (Set.range (modelSwapRel n))) swapA3 (by
      show Ideal.span (Set.range (modelSwapRel n))
        = (Ideal.span (Set.range (fermatModelRel n))).map (swapA3 : A3 →+* A3)
      rw [map_span_fermatModelRel])

/-- **y-侧局部化模型也是相对维数 1 的 standard smooth**（沿 x↔y 对称性从 r-侧运输）。 -/
theorem modelSwap_isStandardSmooth (n : Nat) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (ModelSwap n) := by
  haveI := fermatModel_isStandardSmooth n
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (1) (ModelSwapEquiv n)

#print axioms image_fermatModelRel_under_swap
#print axioms map_span_fermatModelRel
#print axioms ModelSwapEquiv
#print axioms modelSwap_isStandardSmooth


end LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartSwapActual