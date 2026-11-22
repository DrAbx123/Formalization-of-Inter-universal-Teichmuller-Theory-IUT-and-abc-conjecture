import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# The finite-place theta-pilot scaled region

This file realizes the source region `q ^ j^2 * O_hol` of IUT IV, Step (v),
inside the actual tuple tensor block `ArithmeticTensorTupleBlock places tuple`.
The pilot factor is the pure tensor
`arithmeticTupleSingleFractionalGenerator`; it is a tensor element, not a
unit, a log-shell element, or a value-monoid object.

The holomorphic region is the integral closure of `Zp` in the tensor block.
Its set carrier is the canonical unit reference by
`arithmeticTupleCanonicalUnitReference_eq_integralClosure`.

For Kepler's interface, the intended instance is

* `E := fun mu => arithmeticTupleSingleFractionalLattice places tuple iSelected mu`,
* `N` an arbitrary normalization submodule, and
* `varpi := arithmeticTupleThetaPilotGenerator places tuple iSelected q weight`.

The theorem `arithmeticTupleThetaPilotRegion_le_singleCoordinateFractional`
delivers the source-region inclusion
`thetaPilotRegion <= E mu * N`.  Kepler's `hspanN` has the opposite direction
`E lambda * N <= span {varpi} * N`; it is not a consequence of that inclusion.
When the pilot generator has exact radius and `R * N = N`, the existing exact
generator equality in `FinitePlaceFractionalTensorLattice` supplies the
corresponding equality with `span {varpi}`, but no converse is asserted here.

## 交接状态（2026-10-18）

- 文件：`D:\lean\LeanFormal\IUT\ABCBridge\Geometry\FinitePlaceThetaPilotScaledRegion.lean`
- 最后构建：`D:\lean\tmp\n4n7-consolidation-20261017\thetapilot-scaled-region-build3.log`；
  `exit=0`，`3640 jobs`。六条 `#print axioms` 已使用完整命名空间，探针解析正常。
- 已 proved：
  `arithmeticTupleThetaPilotGenerator`、
  `arithmeticTupleThetaPilotRegion`、
  `arithmeticTupleThetaPilotExponent_nonneg`、
  `arithmeticTupleThetaPilotGenerator_mem_singleFractionalLattice`、
  `arithmeticTupleThetaPilotRegion_le_singleCoordinateFractional`、
  `arithmeticTupleThetaPilotExactRadius`。
  公理均为 `[propext, Classical.choice, Quot.sound]`。
- 未完成：`(5)` 只证明 `thetaPilotRegion <= E mu * N`，没有证明 Kepler 所需的
  反向 `E lambda * N <= span {varpi} * N`；`arithmeticTupleThetaPilotExactRadius`
  显式接收 `hradius`，尚未补上候选估值到归一化范数的桥；区域包含定理中的
  `_hNN : N * N <= N` 目前未被使用，文件仍有未使用 section variable 与长行 linter 警告。
- 下一步精确动作：在该文件（保持唯一 owner）复用
  `arithmeticTupleSingleFractionalLattice_mul_eq_map_mulLeft_of_norm_eq` 和
  `arithmeticTupleSubmodule_span_singleton_mul_eq_map_mulLeft`，在
  `hexact : ||q ^ weight|| = p ^ (-lambda)` 与
  `hN : arithmeticTupleValuationIntegerLattice places tuple * N = N` 下新增
  exact-generator 的 `hspanN` 等式/包含，取 `varpi` 为该 pilot generator；
  然后仅重建本文件并复核 `#print axioms`。本轮不新增声明。
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm
open scoped Pointwise

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The Step (v) pilot generator `q ^ weight` placed in the selected tensor
coordinate and with `1` in every other coordinate. -/
def arithmeticTupleThetaPilotGenerator (iSelected : ι)
    (q : CommonPrimeCompletion (places iSelected (tuple iSelected))) (weight : ℕ) :
    ArithmeticTensorTupleBlock places tuple :=
  arithmeticTupleSingleFractionalGenerator places tuple iSelected (q ^ weight)

/-- The actual scaled holomorphic region `q ^ weight * O_hol`.  The carrier of
the second factor is `arithmeticTupleCanonicalUnitReference`, the integral
closure of `Zp` in the tensor block. -/
def arithmeticTupleThetaPilotRegion (iSelected : ι)
    (q : CommonPrimeCompletion (places iSelected (tuple iSelected))) (weight : ℕ) :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Submodule.span ℤ_[p]
      ({arithmeticTupleThetaPilotGenerator places tuple iSelected q weight} :
        Set (ArithmeticTensorTupleBlock places tuple)) *
    (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).toSubmodule

/-- A positive pilot weight and a positive local order give a nonnegative
pilot exponent. -/
theorem arithmeticTupleThetaPilotExponent_nonneg
    {weight : ℕ} {lambda : ℝ} (_hweight : 0 < weight) (hlambda : 0 < lambda) :
    0 ≤ (weight : ℝ) * lambda :=
  mul_nonneg (Nat.cast_nonneg weight) (le_of_lt hlambda)

/-- If the selected pilot power has the required fractional norm bound, then
the corresponding pure tensor lies in the single-coordinate fractional
lattice.  At all nonselected coordinates the tensor coordinate is `1`, whose
norm is at most `p ^ 0`. -/
theorem arithmeticTupleThetaPilotGenerator_mem_singleFractionalLattice
    (iSelected : ι) (q : CommonPrimeCompletion (places iSelected (tuple iSelected)))
    (weight : ℕ) {mu : ℝ}
    (hq : ‖q ^ weight‖ ≤ (p : ℝ) ^ (-mu)) :
    arithmeticTupleThetaPilotGenerator places tuple iSelected q weight ∈
      arithmeticTupleSingleFractionalLattice places tuple iSelected mu := by
  rw [arithmeticTupleThetaPilotGenerator, arithmeticTupleSingleFractionalLattice,
    arithmeticTupleSingleFractionalGenerator, arithmeticTupleFractionalLattice]
  apply arithmeticTupleFractionalLattice_pure_tensor_mem
  intro i
  by_cases hi : i = iSelected
  · subst i
    simpa [Pi.mulSingle_eq_same, arithmeticTupleSingleFractionalExponent,
      mem_padicFractionalLattice_iff] using hq
  · rw [Pi.mulSingle_eq_of_ne hi, arithmeticTupleSingleFractionalExponent_ne hi,
      mem_padicFractionalLattice_iff]
    simp

/-- The scaled pilot region is contained in the corresponding single-coordinate
fractional lattice times any normalization submodule containing `O_hol`. -/
theorem arithmeticTupleThetaPilotRegion_le_singleCoordinateFractional
    (iSelected : ι) (q : CommonPrimeCompletion (places iSelected (tuple iSelected)))
    (weight : ℕ) {mu : ℝ}
    (hq : ‖q ^ weight‖ ≤ (p : ℝ) ^ (-mu))
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (hO : (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).toSubmodule ≤ N)
    (_hNN : N * N ≤ N) :
    arithmeticTupleThetaPilotRegion places tuple iSelected q weight ≤
      arithmeticTupleSingleFractionalLattice places tuple iSelected mu * N := by
  have hgen := arithmeticTupleThetaPilotGenerator_mem_singleFractionalLattice
    places tuple iSelected q weight hq
  have hspan : Submodule.span ℤ_[p]
        ({arithmeticTupleThetaPilotGenerator places tuple iSelected q weight} :
          Set (ArithmeticTensorTupleBlock places tuple)) ≤
      arithmeticTupleSingleFractionalLattice places tuple iSelected mu := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hgen
  rw [arithmeticTupleThetaPilotRegion]
  exact mul_le_mul' hspan hO

/-- The exact-radius form of a finite-place `q`-candidate.  The radius equality
is an explicit hypothesis: the bridge from the candidate valuation to the
normalized norm is not manufactured here. -/
theorem arithmeticTupleThetaPilotExactRadius
    (iSelected : ι)
    (parameter : LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceQCandidate
      (places iSelected (tuple iSelected)).val)
    (hradius : ‖(parameter.q :
        CommonPrimeCompletion (places iSelected (tuple iSelected)))‖ =
      (p : ℝ) ^ (-(parameter.exponent : ℝ))) :
    0 < parameter.exponent ∧
      ‖(parameter.q :
        CommonPrimeCompletion (places iSelected (tuple iSelected)))‖ =
        (p : ℝ) ^ (-(parameter.exponent : ℝ)) :=
  ⟨parameter.exponent_pos, hradius⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace

#print axioms LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleThetaPilotGenerator
#print axioms LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleThetaPilotRegion
#print axioms LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleThetaPilotExponent_nonneg
#print axioms LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleThetaPilotGenerator_mem_singleFractionalLattice
#print axioms LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleThetaPilotRegion_le_singleCoordinateFractional
#print axioms LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleThetaPilotExactRadius
