import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceUnscaledLogTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

/-!
# Tensorization of the local paper inclusions

Curie's `IntegralLogShellSharpBounds` proves the two local inclusions of
Paper IV Proposition 1.2(i) on the actual unscaled carrier:

* `padicFractionalLattice a_i <= unitLogLattice`;
* `unitLogLattice <= padicFractionalLattice (-b_i)`.

This file tensors those statements over the tuple of finite places.  The
tensor lattice is the actual `submoduleTensorSpan`; the proof is the existing
`submoduleTensorSpan_mono`, applied coordinatewise.

The order-theoretic Step (v) interface is also recorded.  Its product
compatibility hypothesis `hprod` is not a formal consequence of the two local
inclusions: the norm-ball exponents can round when multiplied, and the
existing `arithmeticTupleFractionalLattice_mul_mul_le` has the opposite
containment direction.  `hprod` is the precise extra input consumed by
Kepler's `hNA` input; it is intended to be discharged by the exact-generator /
`O_hol` normalization construction, not by monotonicity alone.

## 交接状态（2026-10-18）

- 文件: `D:\lean\LeanFormal\IUT\ABCBridge\Geometry\FinitePlaceLocalInclusionTensorization.lean`
- 最后构建: `D:\lean\tmp\n4n7-consolidation-20261017\local-inclusion-tensorization-build4.log`，guard exit=0，3651 jobs；本文件 2 条 warning（未使用的 `[∀ i, Fintype (V i)]` section variable；未使用的 `ha`）。
- 已 proved: `arithmeticTupleFractionalLattice_paperA_le_unitLogLattice`、`arithmeticTupleUnitLogLattice_le_fractionalLattice_neg_paperB`；两条均为 `[propext, Classical.choice, Quot.sound]`。
- 未完成: 旧定理 `arithmeticTupleFractionalLattice_mul_le_unitLogLattice_of_local` 及其 `hprod`、`ha` 仍在文件中，尚未删除；整数标量接口 a)–d) 与 `arithmeticTuplePaperScaledNormalization` 尚未实现；build5 未运行。
- 下一步精确动作: 先删除旧定理、`hprod`、`ha` 及其 `#print axioms`，并移除未使用的 `[∀ i, Fintype (V i)]`；再实现 a)–d) 与合成引理。
- 数学阻塞（a）: 冻结形式 `(m:ℝ) ≥ ∑ i, c i` 对一般实值 `c` 不成立。反例: `K = ℚ_[p]`、两坐标、`c = (1/2,1/2)`、`m = 1`；此时 `padicFractionalLattice (1/2) = pℤ_[p]`，故 `F c = pℤ_[p] ⊗ pℤ_[p] = p² R_I`，而 `p^1 R_I = pℤ_[p] ⊗ ℤ_[p]`，且 `p ⊗ 1 ∉ p²(ℤ_[p] ⊗ ℤ_[p])`。
- 最小修正: 将 a) 的假设加强为逐坐标 `∑ i, ⌈c i⌉ ≤ m`；或保留 `m ≥ ∑ c i` 并增加 `arithmeticTupleHasExactFractionalGenerators places tuple c`（论文 A/B 指数位于局部值群，可用 `logShellPaperAlphaElement` / `logShellPaperBetaElement` 和 `IsDiscreteValuationRing.exists_irreducible` 选出的 uniformizer 实现）。
- 共享环境构建: `trace-dual-paper-build15b.log`（`IntegralTraceDualTensorInclusion`，非本文件）guard exit=1，3671 jobs，失败点 `IntegralTraceDualTensorInclusion.lean:684:77`。
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm
open scoped LeanFormal.IUT.FinitePadicIntegralLattice Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The local paper A exponent at coordinate `i`, bound to the actual
ramification exponent of the completion. -/
abbrev arithmeticTupleLocalPaperAExponent (i : ι) : ℝ :=
  logShellPaperAExponent p
    (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- The local paper B exponent at coordinate `i`, bound to the actual
ramification exponent of the completion. -/
abbrev arithmeticTupleLocalPaperBExponent (i : ι) : ℝ :=
  logShellPaperBExponent p
    (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- Paper IV Proposition 1.2(i), lower inclusion, tensorized over the actual
tuple of finite places. -/
theorem arithmeticTupleFractionalLattice_paperA_le_unitLogLattice :
    arithmeticTupleFractionalLattice places tuple
        (fun i => arithmeticTupleLocalPaperAExponent places tuple i) ≤
      arithmeticTupleUnitLogLattice places tuple := by
  unfold arithmeticTupleFractionalLattice arithmeticTupleUnitLogLattice
  apply submoduleTensorSpan_mono
  intro i
  exact padicFractionalLattice_paperA_le_unitLogLattice
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)

/-- Paper IV Proposition 1.2(i), upper inclusion, tensorized over the actual
tuple of finite places. -/
theorem arithmeticTupleUnitLogLattice_le_fractionalLattice_neg_paperB :
    arithmeticTupleUnitLogLattice places tuple ≤
      arithmeticTupleFractionalLattice places tuple
        (fun i => -arithmeticTupleLocalPaperBExponent places tuple i) := by
  unfold arithmeticTupleFractionalLattice arithmeticTupleUnitLogLattice
  apply submoduleTensorSpan_mono
  intro i
  exact unitLogLattice_le_padicFractionalLattice_neg_paperB
    (K := CommonPrimeCompletion (places i (tuple i))) (p := p)

local instance localInclusionTensorizationZpAlgebra :
    Algebra ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  Algebra.restrictScalars ℤ_[p] ℚ_[p] (ArithmeticTensorTupleBlock places tuple)

/-- Order-theoretic Step (v) interface.

The hypotheses `hA` and `hN` are the tensorized lower inclusion and the
normalization containment.  The product-compatibility hypothesis `hprod` is
the extra step needed to pass from `F d * N` to `F (d+a) * N`; without it the
only available lattice inequality is the reverse one,
`F a * (F d * N) <= F (d+a) * N` (`arithmeticTupleFractionalLattice_mul_mul_le`).
The conclusion is exactly Kepler's `hNA` input. -/
theorem arithmeticTupleFractionalLattice_mul_le_unitLogLattice_of_local
    {d a : ι → ℝ}
    {N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)}
    (ha : ∀ i, 0 ≤ a i)
    (hA : arithmeticTupleFractionalLattice places tuple a ≤
      arithmeticTupleUnitLogLattice places tuple)
    (hN : arithmeticTupleFractionalLattice places tuple d * N ≤
      arithmeticTupleValuationIntegerLattice places tuple)
    (hprod : arithmeticTupleFractionalLattice places tuple (fun i => d i + a i) * N ≤
      arithmeticTupleFractionalLattice places tuple a *
        (arithmeticTupleFractionalLattice places tuple d * N)) :
    arithmeticTupleFractionalLattice places tuple (fun i => d i + a i) * N ≤
      arithmeticTupleUnitLogLattice places tuple := by
  calc
    arithmeticTupleFractionalLattice places tuple (fun i => d i + a i) * N
        ≤ arithmeticTupleFractionalLattice places tuple a *
            (arithmeticTupleFractionalLattice places tuple d * N) := hprod
    _ ≤ arithmeticTupleFractionalLattice places tuple a *
          arithmeticTupleValuationIntegerLattice places tuple :=
      mul_le_mul' le_rfl hN
    _ ≤ arithmeticTupleFractionalLattice places tuple a :=
      arithmeticTupleFractionalLattice_mul_valuationInteger_le places tuple a
    _ ≤ arithmeticTupleUnitLogLattice places tuple := hA

#print axioms arithmeticTupleFractionalLattice_paperA_le_unitLogLattice
#print axioms arithmeticTupleUnitLogLattice_le_fractionalLattice_neg_paperB
#print axioms arithmeticTupleFractionalLattice_mul_le_unitLogLattice_of_local

end

end LeanFormal.IUT.NumberFieldFinitePlace
