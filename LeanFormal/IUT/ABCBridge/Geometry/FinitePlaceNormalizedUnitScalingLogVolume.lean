import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceHolomorphicIntegralClosure
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Degree-normalized log-volume for multi-coordinate fractional shifts

The normalization is the one in IUT IV Proposition 1.4(i): the raw Haar
log-ratio is divided by `D = finrank_{Q_p} X`.  For a multi-coordinate
fractional lattice `F c` with an exact pure-tensor generator `beta`, the main
theorem computes the normalized log-volume of `(F c) * O_hol` exactly:

`mu_log ((F c) * O_hol) = -(sum_i c_i) * log p`.

The value-group realization of the local generators is an explicit hypothesis
in this file.  Its purpose is to isolate the Haar/log-volume computation from
the local ramification bookkeeping `(1/e_i) Z`.  In the intended application
`c_i` lies in `(1/e_i) Z`, a common multiple `E` of the denominators makes
`E * c_i` integral, and the exact local generators are supplied by the
value-group argument.  No tensor determinant or Smith normal form is assumed.

## 交接状态（2026-10-18，Noether；接管自 Bohr 实例）

- 文件：`D:\lean\LeanFormal\IUT\ABCBridge\Geometry\FinitePlaceNormalizedUnitScalingLogVolume.lean`
  （本协作轮唯一 owner，consolidation §37 登记）。
- 最后构建：`D:\lean\tmp\n4n7-consolidation-20261017\normalized-unit-scaling-volume-build8.log`，
  guard exit=0，`Build completed successfully (3643 jobs)`；本文件 warning 0（日志中 6 条
  warning 均属依赖文件），无 `sorryAx`。日志内 3 条显式 `#print axioms`
  （`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`、
  `arithmeticTupleNormalizedLogVolume_primeScalar_zpow`、
  `arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul`）
  均为 `[propext, Classical.choice, Quot.sound]`。
- 本实例接手后未新增任何声明。以下三条目标尚未开始、尚未证明：
  1. `arithmeticTupleNormalizedLogVolume_primePowerScale`：
     `mu_log (p^k • O_hol) = -(k : ℝ) * Real.log p`。路径：先把
     `Submodule.map (mulLeft ((p : ℚ_[p]) ^ k))` 与
     `(↑(arithmeticTuplePrimeScalarUnit ^ k) : ArithmeticTensorTupleBlock places tuple) • O_hol`
     对齐，再特化既有 `arithmeticTupleNormalizedLogVolume_primeScalar_zpow`（约 L473）。
     Kepler 的 `arithmeticTensorPrimePowerScale` 位于
     `FinitePlaceLogShellScalingAssembly.lean`，本文件不得反向 import（会成环）；
     必要时在本文件写等价定义并在 docstring 注明二者一致。
  2. `arithmeticTupleNormalizedLogVolume_paperEndpoint`：取
     `m0 = ⌊λ⌋ - ⌈Σd⌉ - ⌈Σa⌉`（先求和再取整），
     `mu_log (p^(m0 - ⌈Σb⌉) • O_hol) = -((m0 : ℝ) - ⌈Σb⌉) * Real.log p`，
     由第 1 条以 `k = m0 - ⌈Σb⌉` 特化。
  3. `arithmeticTupleNormalizedLogVolume_paperEndpoint_le`：
     `mu_log (p^(m0 - ⌈Σb⌉) • O_hol) ≤ (-λ + Σd + Σa + Σb + 4) * Real.log p`，
     用 `⌊λ⌋ ≥ λ - 1`、`⌈Σd⌉ ≤ Σd + 1`、`⌈Σa⌉ ≤ Σa + 1`、`⌈Σb⌉ ≤ Σb + 1`
     与 `Real.log p > 0` 线性组合。若需 `m0` 本地定义，命名
     `arithmeticTupleVolumePaperExponent` 并显式给出等式。
- 下一步精确动作：先实现第 1 条并跑 guard（build9），再依次完成第 2、3 条（build10），
  文件末尾 `#print axioms` 覆盖三条新声明，要求 warning 0、无 `sorryAx`。
- 本段是收工时的注释性追加；build8 证据对应追加前的声明集合，追加不改变任何声明。
- 收尾复验：`D:\lean\tmp\n4n7-consolidation-20261017\normalized-unit-scaling-volume-build9.log`，
  guard exit=0，`Build completed successfully (3643 jobs)`；本文件 warning 0，无 `sorryAx`；
  3 条 `#print axioms` 仍为 `[propext, Classical.choice, Quot.sound]`。该构建在上一段
  交接文字追加后通过；本行是其后唯一的 docstring 文字追加，不涉及任何声明。
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open LeanFormal.IUT.LocalFieldPadicTensor
open scoped Pointwise NNReal ENNReal

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- The holomorphic integer lattice `O_hol`, realized as the integral closure of
`Z_p` in the tensor block.  Its carrier is the canonical unit reference. -/
abbrev arithmeticTupleHolomorphicLattice : Submodule ℤ_[p]
    (ArithmeticTensorTupleBlock places tuple) :=
  (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).toSubmodule

set_option linter.unusedFintypeInType false in
theorem coefficient_arithmeticTupleHolomorphicLattice :
    (arithmeticTupleHolomorphicLattice places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      arithmeticTupleCanonicalUnitReference places tuple := by
  simpa [arithmeticTupleHolomorphicLattice] using
    (arithmeticTupleCanonicalUnitReference_eq_integralClosure places tuple).symm

/-- The degree-normalized logarithmic Haar volume used by IUT IV Proposition
1.4(i).  It is defined for every set; the theorems below use it only on sets
of positive finite Haar mass. -/
def arithmeticTupleNormalizedLogVolume
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    (S : Set (ArithmeticTensorTupleBlock places tuple)) : ℝ :=
  (1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)) *
    (Real.log (μ S).toReal - Real.log
      (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal)

theorem arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      (arithmeticTupleCanonicalUnitReference places tuple) = 0 := by
  simp [arithmeticTupleNormalizedLogVolume]

theorem arithmeticTupleNormalizedLogVolume_mono
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    {S T : Set (ArithmeticTensorTupleBlock places tuple)}
    (hST : S ⊆ T) (hSpos : 0 < μ S) (hTfin : μ T < ⊤) :
    arithmeticTupleNormalizedLogVolume places tuple μ S ≤
      arithmeticTupleNormalizedLogVolume places tuple μ T := by
  have hDpos : (0 : ℝ) < (Module.finrank ℚ_[p]
      (ArithmeticTensorTupleBlock places tuple) : ℝ) := by
    exact_mod_cast finrank_arithmeticTensorTupleBlock_pos places tuple
  have hSfin : μ S < ⊤ := lt_of_le_of_lt (measure_mono hST) hTfin
  have hlog : Real.log (μ S).toReal ≤ Real.log (μ T).toReal :=
    Real.log_le_log (ENNReal.toReal_pos hSpos.ne' hSfin.ne)
      (ENNReal.toReal_mono hTfin.ne (measure_mono hST))
  have hinv : 0 ≤ 1 / (Module.finrank ℚ_[p]
      (ArithmeticTensorTupleBlock places tuple) : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hlog _) hinv

/-- The value-group data used for the exact multi-coordinate scaling theorem.

`localGenerator i` has normalized norm `p ^ (-(c i))`.  The common positive
integer `E` is a ramification multiple.  At that multiple each local generator
has the form `p ^ (integerExponent i) * unit`, with a norm-one local unit.  The
pure tensor of these local units acts trivially on `O_hol`.  These fields are
the explicit interface replacing the not-yet-integrated `(1/e_i) Z`
realization. -/
structure ArithmeticTuplePureFractionalScalingData (c : ι → ℝ) where
  localGenerator : (i : ι) → CommonPrimeCompletion (places i (tuple i))
  localGenerator_norm : ∀ i, ‖localGenerator i‖ = (p : ℝ) ^ (-(c i))
  commonExponent : ℕ
  commonExponent_pos : 0 < commonExponent
  integerExponent : ι → ℤ
  localUnit : (i : ι) → CommonPrimeCompletion (places i (tuple i))
  localUnit_norm : ∀ i, ‖localUnit i‖ = 1
  localGenerator_pow : ∀ i,
    localGenerator i ^ commonExponent =
      (p : CommonPrimeCompletion (places i (tuple i))) ^ (integerExponent i) *
        localUnit i
  order_eq : ∀ i, (c i) * (commonExponent : ℝ) = (integerExponent i : ℝ)
  unitTensor_action :
    (arithmeticTupleFractionalPureGenerator places tuple localUnit) •
        arithmeticTupleCanonicalUnitReference places tuple =
      arithmeticTupleCanonicalUnitReference places tuple
  integerTensor_mul_holomorphic :
    arithmeticTupleValuationIntegerLattice places tuple *
        arithmeticTupleHolomorphicLattice places tuple =
      arithmeticTupleHolomorphicLattice places tuple

theorem arithmeticTuplePureFractionalScalingData_localGenerator_ne_zero
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) (i : ι) :
    data.localGenerator i ≠ 0 := by
  intro hzero
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpos : 0 < (p : ℝ) ^ (-(c i)) := Real.rpow_pos_of_pos hp _
  have hnorm := data.localGenerator_norm i
  rw [hzero, norm_zero] at hnorm
  exact hpos.ne' hnorm.symm

theorem arithmeticTuplePureFractionalScalingData_localUnit_ne_zero
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) (i : ι) :
    data.localUnit i ≠ 0 := by
  intro hzero
  have hnorm := data.localUnit_norm i
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The pure-tensor product as a monoid homomorphism. -/
def arithmeticTuplePureTensorMulHom :
    ((i : ι) → CommonPrimeCompletion (places i (tuple i))) →*
      ArithmeticTensorTupleBlock places tuple :=
  PiTensorProduct.tprodMonoidHom (R := ℚ_[p])

omit [Fintype ι] in
theorem arithmeticTuplePureTensorMulHom_apply
    (x : (i : ι) → CommonPrimeCompletion (places i (tuple i))) :
    arithmeticTuplePureTensorMulHom places tuple x =
      finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i))) x := rfl

/-- The local generator as a unit of its local field. -/
def arithmeticTupleFractionalLocalGeneratorUnit
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) (i : ι) :
    (CommonPrimeCompletion (places i (tuple i)))ˣ :=
  Units.mk0 (data.localGenerator i)
    (arithmeticTuplePureFractionalScalingData_localGenerator_ne_zero places tuple data i)

/-- The local unit as a unit of its local field. -/
def arithmeticTupleFractionalLocalUnit
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) (i : ι) :
    (CommonPrimeCompletion (places i (tuple i)))ˣ :=
  Units.mk0 (data.localUnit i)
    (arithmeticTuplePureFractionalScalingData_localUnit_ne_zero places tuple data i)

/-- The pure tensor of the local generators, as a unit of the tensor block. -/
def arithmeticTupleFractionalGeneratorUnit
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    (ArithmeticTensorTupleBlock places tuple)ˣ :=
  Units.map (arithmeticTuplePureTensorMulHom places tuple)
    (MulEquiv.piUnits.symm
      (arithmeticTupleFractionalLocalGeneratorUnit places tuple data))

/-- The pure tensor of the local units, as a unit of the tensor block. -/
def arithmeticTupleFractionalUnitTensorUnit
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    (ArithmeticTensorTupleBlock places tuple)ˣ :=
  Units.map (arithmeticTuplePureTensorMulHom places tuple)
    (MulEquiv.piUnits.symm
      (arithmeticTupleFractionalLocalUnit places tuple data))

theorem arithmeticTupleFractionalGeneratorUnit_coe
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    (↑(arithmeticTupleFractionalGeneratorUnit places tuple data) :
        ArithmeticTensorTupleBlock places tuple) =
      arithmeticTupleFractionalPureGenerator places tuple data.localGenerator := rfl

theorem arithmeticTupleFractionalUnitTensorUnit_coe
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    (↑(arithmeticTupleFractionalUnitTensorUnit places tuple data) :
        ArithmeticTensorTupleBlock places tuple) =
      arithmeticTupleFractionalPureGenerator places tuple data.localUnit := rfl

omit [Fintype ι] in
/-- The pure tensor of a family of local generators raised to a natural power
is the pure tensor of the coordinatewise powers. -/
theorem arithmeticTupleFractionalPureGenerator_pow
    (c : (i : ι) → CommonPrimeCompletion (places i (tuple i))) (n : ℕ) :
    (arithmeticTupleFractionalPureGenerator places tuple c) ^ n =
      arithmeticTupleFractionalPureGenerator places tuple (fun i => c i ^ n) := by
  rw [arithmeticTupleFractionalPureGenerator, arithmeticTupleFractionalPureGenerator]
  rw [← arithmeticTuplePureTensorMulHom_apply, ← arithmeticTuplePureTensorMulHom_apply]
  exact (map_pow (arithmeticTuplePureTensorMulHom places tuple) c n).symm

/-- A pure tensor of prime powers is the corresponding base-field scalar times
the tensor unit.  Only the sum of the integer exponents occurs. -/
theorem arithmeticTupleTprod_prime_zpow_eq_scalar
    (n : ι → ℤ) :
    finitePadicTensorTprod (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i)))
        (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ (n i)) =
      ((p : ℚ_[p]) ^ (∑ i, n i)) •
        (1 : ArithmeticTensorTupleBlock places tuple) := by
  have hsmul : (fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^ (n i)) =
      fun i => ((p : ℚ_[p]) ^ (n i)) • (1 : CommonPrimeCompletion (places i (tuple i))) := by
    funext i
    rw [Algebra.smul_def, mul_one]
    rw [← map_natCast (algebraMap ℚ_[p] (CommonPrimeCompletion (places i (tuple i)))) p]
    exact (map_zpow₀ (algebraMap ℚ_[p] (CommonPrimeCompletion (places i (tuple i))))
      (p : ℚ_[p]) (n i)).symm
  rw [hsmul]
  have hmap := MultilinearMap.map_smul_univ
    (finitePadicTensorTprod (p := p)
      (fun i => CommonPrimeCompletion (places i (tuple i))))
    (fun i => (p : ℚ_[p]) ^ (n i))
    (fun i => (1 : CommonPrimeCompletion (places i (tuple i))))
  rw [hmap]
  have hprod : (∏ i, (p : ℚ_[p]) ^ (n i)) = (p : ℚ_[p]) ^ (∑ i, n i) := by
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
        rw [zpow_add₀]
        exact Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  rw [hprod]
  have hone : finitePadicTensorTprod (p := p)
      (fun i => CommonPrimeCompletion (places i (tuple i))) (fun i => 1) =
      (1 : ArithmeticTensorTupleBlock places tuple) := by
    change PiTensorProduct.tprod ℚ_[p]
      (fun i => (1 : CommonPrimeCompletion (places i (tuple i)))) = 1
    exact PiTensorProduct.one_def.symm
  rw [hone]

/-- The exact-generator identification of the multi-coordinate fractional
lattice product with the multiplicative translate of `O_hol`. -/
theorem arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    ((arithmeticTupleFractionalLattice places tuple c *
        arithmeticTupleHolomorphicLattice places tuple :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator) •
        arithmeticTupleCanonicalUnitReference places tuple := by
  have hspan := arithmeticTupleFractionalLattice_eq_valuationInteger_mul_span_of_norm_eq
    places tuple c data.localGenerator data.localGenerator_norm
  have hmul := arithmeticTupleFractionalLattice_mul_eq_map_mulLeft_of_eq_valuationInteger_mul_span
    places tuple c (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator)
    (arithmeticTupleHolomorphicLattice places tuple) hspan data.integerTensor_mul_holomorphic
  rw [hmul, Submodule.map_coe, coefficient_arithmeticTupleHolomorphicLattice]
  ext x
  simp [Set.mem_smul_set, LinearMap.mulLeft_apply, smul_eq_mul]

local instance arithmeticTupleUnitsContinuousConstSMul :
    ContinuousConstSMul (ArithmeticTensorTupleBlock places tuple)ˣ
      (ArithmeticTensorTupleBlock places tuple) := by
  refine ⟨fun u => ?_⟩
  change Continuous (fun x : ArithmeticTensorTupleBlock places tuple =>
    (u : ArithmeticTensorTupleBlock places tuple) * x)
  exact (LinearMap.mulLeft ℚ_[p]
    (u : ArithmeticTensorTupleBlock places tuple)).continuous_of_finiteDimensional

/-- The canonical unit inducing multiplication by the rational prime `p`. -/
abbrev arithmeticTuplePrimeScalarUnit :
    (ArithmeticTensorTupleBlock places tuple)ˣ :=
  Units.map (algebraMap ℚ_[p] (ArithmeticTensorTupleBlock places tuple)).toMonoidHom
    (LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit (p := p))

/-- The character of the base-prime scalar unit is the inverse `D`-th power
of `p`. -/
theorem distribHaarChar_arithmeticTuplePrimeScalarUnit
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)] :
    distribHaarChar (ArithmeticTensorTupleBlock places tuple)
        (arithmeticTuplePrimeScalarUnit places tuple) =
      ((p : ℝ≥0) ^ Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple))⁻¹ := by
  let X := ArithmeticTensorTupleBlock places tuple
  let μ : Measure X := Measure.addHaar
  let H := arithmeticTupleCanonicalUnitReference places tuple
  have hmass := measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ
  have hpos : 0 < μ H := hmass.2.1
  have hfin : μ H < ⊤ := hmass.2.2
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := H)
    (g := arithmeticTuplePrimeScalarUnit places tuple)
    (r := ((p : ℝ≥0) ^ Module.finrank ℚ_[p] X)⁻¹) hpos.ne' hfin.ne
  have hset : arithmeticTuplePrimeScalarUnit places tuple • H = (p : ℚ_[p]) • H := by
    have hunit : (↑(arithmeticTuplePrimeScalarUnit places tuple) : X) =
        algebraMap ℚ_[p] X (p : ℚ_[p]) := by
      change (algebraMap ℚ_[p] X)
        (↑(LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit
          (p := p)) : ℚ_[p]) = algebraMap ℚ_[p] X (p : ℚ_[p])
      rw [show (↑(LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit
          (p := p)) : ℚ_[p]) = (p : ℚ_[p]) from Units.val_mk0 _]
    have hsmul_eq : ∀ y : X, (p : ℚ_[p]) • y =
        (↑(arithmeticTuplePrimeScalarUnit places tuple) : X) * y := by
      intro y
      rw [Algebra.smul_def, hunit]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, hsmul_eq y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (hsmul_eq y).symm⟩
  rw [hset, LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := p) μ H]
  have hfactor : ((p : ℝ≥0) ^ Module.finrank ℚ_[p] X) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  rw [ENNReal.coe_inv hfactor, ENNReal.coe_pow, ENNReal.coe_natCast]

/-- The real logarithmic character of `p ^ k` acting on the full tensor block. -/
theorem real_log_distribHaarChar_arithmeticTuplePrimeScalarUnit_zpow
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)] (k : ℤ) :
    Real.log (distribHaarChar (ArithmeticTensorTupleBlock places tuple)
      ((arithmeticTuplePrimeScalarUnit places tuple) ^ k) : ℝ) =
      -((k : ℝ) * (Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple) : ℝ) * Real.log (p : ℝ)) := by
  rw [map_zpow, distribHaarChar_arithmeticTuplePrimeScalarUnit]
  simp only [NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast]
  have hpow : ((p : ℝ) ^ Module.finrank ℚ_[p]
      (ArithmeticTensorTupleBlock places tuple))⁻¹ ^ k =
      (p : ℝ) ^ (-(k * (Module.finrank ℚ_[p]
        (ArithmeticTensorTupleBlock places tuple) : ℤ))) := by
    rw [inv_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    ring
  rw [hpow]
  rw [Real.log_zpow]
  push_cast
  ring

/-- Exact normalized volume of the pure-tensor fractional product with
`O_hol`, under the explicit value-group scaling data. -/
theorem arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      ((arithmeticTupleFractionalLattice places tuple c *
        arithmeticTupleHolomorphicLattice places tuple :
          Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
        Set (ArithmeticTensorTupleBlock places tuple)) =
      -((∑ i, c i) * Real.log (p : ℝ)) := by
  let X := ArithmeticTensorTupleBlock places tuple
  let O := arithmeticTupleCanonicalUnitReference places tuple
  let β := arithmeticTupleFractionalPureGenerator places tuple data.localGenerator
  let M : ℤ := ∑ i, data.integerExponent i
  let pU : Xˣ := arithmeticTuplePrimeScalarUnit places tuple
  let βU : Xˣ := arithmeticTupleFractionalGeneratorUnit places tuple data
  let uU : Xˣ := arithmeticTupleFractionalUnitTensorUnit places tuple data
  have hDne : (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) ≠ 0 := by
    exact_mod_cast (finrank_arithmeticTensorTupleBlock_pos places tuple).ne'
  have hμO := measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ
  have hOpos : 0 < μ O := hμO.2.1
  have hOfin : μ O < ⊤ := hμO.2.2
  have hμOreal : (μ O).toReal ≠ 0 := (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hβU_coe : (↑βU : X) = β :=
    arithmeticTupleFractionalGeneratorUnit_coe places tuple data
  have huU_coe : (↑uU : X) =
      arithmeticTupleFractionalPureGenerator places tuple data.localUnit :=
    arithmeticTupleFractionalUnitTensorUnit_coe places tuple data
  have hpow_val : (↑(βU ^ data.commonExponent) : X) = (↑(pU ^ M) : X) * (↑uU : X) := by
    rw [Units.val_pow_eq_pow_val, hβU_coe]
    change (arithmeticTupleFractionalPureGenerator places tuple data.localGenerator) ^
        data.commonExponent = _
    rw [arithmeticTupleFractionalPureGenerator_pow]
    rw [show (fun i => data.localGenerator i ^ data.commonExponent) =
        fun i => (p : CommonPrimeCompletion (places i (tuple i))) ^
          (data.integerExponent i) * data.localUnit i by
      funext i
      exact data.localGenerator_pow i]
    rw [arithmeticTupleFractionalPureGenerator]
    rw [← finitePadicTensorTprod_mul_tprod]
    rw [arithmeticTupleTprod_prime_zpow_eq_scalar]
    rw [huU_coe]
    congr 1
    have hvalz : (↑(pU ^ M) : X) =
        algebraMap ℚ_[p] X ((p : ℚ_[p]) ^ M) := by
      have hmap : pU ^ M =
          Units.map (algebraMap ℚ_[p] X).toMonoidHom
            (LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit
              (p := p) ^ M) := by
        change (Units.map (algebraMap ℚ_[p] X).toMonoidHom
          (LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit
            (p := p))) ^ M =
          Units.map (algebraMap ℚ_[p] X).toMonoidHom
            (LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit
              (p := p) ^ M)
        exact (map_zpow (Units.map (algebraMap ℚ_[p] X).toMonoidHom)
          LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit M).symm
      rw [hmap, Units.coe_map]
      have hval : (↑(LeanFormal.IUT.PadicFiniteCoordinateHaarScaling.padicPrimeFieldUnit
            (p := p) ^ M) : ℚ_[p]) = (p : ℚ_[p]) ^ M := by
        rw [Units.val_zpow_eq_zpow_val]
        exact congrArg (fun z : ℚ_[p] => z ^ M) (Units.val_mk0 _)
      exact congrArg (algebraMap ℚ_[p] X) hval
    rw [hvalz, Algebra.smul_def, mul_one]
  have hsetpow : (↑(βU ^ data.commonExponent) : X) • O = (↑(pU ^ M) : X) • O := by
    rw [hpow_val, mul_smul, huU_coe, data.unitTensor_action]
  have hratio : ((distribHaarChar X βU : ℝ) ^ data.commonExponent) =
      (distribHaarChar X (pU ^ M) : ℝ) := by
    have hNN : distribHaarChar X (βU ^ data.commonExponent) =
        distribHaarChar X (pU ^ M) := by
      refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := O)
        (g := βU ^ data.commonExponent) (r := distribHaarChar X (pU ^ M))
        hOpos.ne' hOfin.ne ?_
      rw [show (βU ^ data.commonExponent) • O = (pU ^ M) • O by
        simpa [Units.smul_def] using hsetpow]
      exact (distribHaarChar_mul μ (pU ^ M) O).symm
    have hpow : distribHaarChar X (βU ^ data.commonExponent) =
        (distribHaarChar X βU) ^ data.commonExponent := map_pow _ _ _
    rw [hpow] at hNN
    exact_mod_cast hNN
  have hlogβ : Real.log (distribHaarChar X βU : ℝ) =
      -((∑ i, c i) * (Module.finrank ℚ_[p] X : ℝ) * Real.log (p : ℝ)) := by
    have hscalar := real_log_distribHaarChar_arithmeticTuplePrimeScalarUnit_zpow
      (places := places) (tuple := tuple) M
    have hlogpow : (data.commonExponent : ℝ) *
        Real.log (distribHaarChar X βU : ℝ) =
        Real.log (distribHaarChar X (pU ^ M) : ℝ) := by
      calc
        (data.commonExponent : ℝ) * Real.log (distribHaarChar X βU : ℝ) =
            Real.log ((distribHaarChar X βU : ℝ) ^ data.commonExponent) := by
          rw [Real.log_pow]
        _ = Real.log (distribHaarChar X (pU ^ M) : ℝ) := by rw [hratio]
    have hMreal : (M : ℝ) = (data.commonExponent : ℝ) * ∑ i, c i := by
      calc
        (M : ℝ) = ∑ i, (data.integerExponent i : ℝ) := by simp [M]
        _ = ∑ i, (c i) * (data.commonExponent : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (data.order_eq i).symm
        _ = (∑ i, c i) * (data.commonExponent : ℝ) := by rw [Finset.sum_mul]
        _ = (data.commonExponent : ℝ) * ∑ i, c i := by ring
    have hEpos : (0 : ℝ) < data.commonExponent := by exact_mod_cast data.commonExponent_pos
    have hlogscalar' : Real.log (distribHaarChar X (pU ^ M) : ℝ) =
        -((M : ℝ) * (Module.finrank ℚ_[p] X : ℝ) * Real.log (p : ℝ)) := by
      simpa [pU] using hscalar
    have hmain : (data.commonExponent : ℝ) * Real.log (distribHaarChar X βU : ℝ) =
        (data.commonExponent : ℝ) *
          (-((∑ i, c i) * (Module.finrank ℚ_[p] X : ℝ) * Real.log (p : ℝ))) := by
      rw [hlogpow, hlogscalar', hMreal]
      ring
    exact mul_left_cancel₀ hEpos.ne' hmain
  have hFβ := arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    places tuple data
  have hβset : (β • O : Set X) = βU • O := by
    rw [← hβU_coe]
    simp [Units.smul_def]
  unfold arithmeticTupleNormalizedLogVolume
  rw [hFβ, hβset]
  rw [← distribHaarChar_mul μ βU O]
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hchar_ne : (distribHaarChar X βU : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := X) (g := βU)).ne'
  rw [Real.log_mul hchar_ne hμOreal]
  rw [hlogβ]
  simp only [X, O]
  field_simp [hDne]
  ring_nf

/-- Integer scalar scaling of `O_hol` in the degree-normalized convention. -/
theorem arithmeticTupleNormalizedLogVolume_primeScalar_zpow
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] (k : ℤ) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      ((↑(arithmeticTuplePrimeScalarUnit places tuple ^ k) :
          ArithmeticTensorTupleBlock places tuple) •
        arithmeticTupleCanonicalUnitReference places tuple) =
      -((k : ℝ) * Real.log (p : ℝ)) := by
  let X := ArithmeticTensorTupleBlock places tuple
  let O := arithmeticTupleCanonicalUnitReference places tuple
  let pU : Xˣ := arithmeticTuplePrimeScalarUnit places tuple
  have hDne : (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) ≠ 0 := by
    exact_mod_cast (finrank_arithmeticTensorTupleBlock_pos places tuple).ne'
  have hμO := measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ
  have hOpos : 0 < μ O := hμO.2.1
  have hOfin : μ O < ⊤ := hμO.2.2
  have hμOreal : (μ O).toReal ≠ 0 := (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  have hset : (↑(pU ^ k) : X) • O = pU ^ k • O := by
    simp [Units.smul_def]
  unfold arithmeticTupleNormalizedLogVolume
  rw [hset]
  rw [← distribHaarChar_mul μ (pU ^ k) O]
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hchar_ne : (distribHaarChar X (pU ^ k) : ℝ) ≠ 0 := by
    exact_mod_cast (distribHaarChar_pos (A := X) (g := pU ^ k)).ne'
  rw [Real.log_mul hchar_ne hμOreal]
  have hlog := real_log_distribHaarChar_arithmeticTuplePrimeScalarUnit_zpow
    (places := places) (tuple := tuple) k
  rw [hlog]
  simp only [O]
  field_simp [hDne]
  ring_nf

/-- Monotonicity corollary for a set contained in the exact multi-coordinate
fractional container. -/
theorem arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c)
    {S : Set (ArithmeticTensorTupleBlock places tuple)}
    (hSpos : 0 < μ S)
    (hsub : S ⊆ ((arithmeticTupleFractionalLattice places tuple c *
      arithmeticTupleHolomorphicLattice places tuple :
        Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
          Set (ArithmeticTensorTupleBlock places tuple))) :
    arithmeticTupleNormalizedLogVolume places tuple μ S ≤
      -((∑ i, c i) * Real.log (p : ℝ)) := by
  let X := ArithmeticTensorTupleBlock places tuple
  let β := arithmeticTupleFractionalPureGenerator places tuple data.localGenerator
  have hcontainerFin : μ (((arithmeticTupleFractionalLattice places tuple c *
      arithmeticTupleHolomorphicLattice places tuple :
        Submodule ℤ_[p] X) : Set X)) < ⊤ := by
    rw [arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
      places tuple data]
    have hcont : Continuous (fun x : X => β * x) :=
      (LinearMap.mulLeft ℚ_[p] β).continuous_of_finiteDimensional
    have hcompact : IsCompact (β • arithmeticTupleCanonicalUnitReference places tuple) := by
      have hset : (β • arithmeticTupleCanonicalUnitReference places tuple) =
          (fun x : X => β * x) '' arithmeticTupleCanonicalUnitReference places tuple := by
        ext x
        simp only [Set.mem_smul_set, Set.mem_image, smul_eq_mul]
        rfl
      rw [hset]
      exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2.image hcont
    exact hcompact.measure_lt_top
  have hmono := arithmeticTupleNormalizedLogVolume_mono places tuple μ hsub hSpos hcontainerFin
  rwa [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ data] at hmono

/-- The single-coordinate inclusion corollary.  The hypothesis `hball` supplies
the exact value-group representative `c` of the single-coordinate norm ball;
the ceiling inequality `t <= sum_i c_i` is the direction needed for the upper
bound. -/
theorem arithmeticTupleNormalizedLogVolume_le_of_subset_singleCoordinate
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    [DecidableEq ι]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    (iSelected : ι) (t : ℝ)
    {c : ι → ℝ} (data : ArithmeticTuplePureFractionalScalingData places tuple c)
    (hceiling : t ≤ ∑ i, c i)
    (hball : arithmeticTupleSingleFractionalLattice places tuple iSelected t =
      arithmeticTupleFractionalLattice places tuple c)
    {S : Set (ArithmeticTensorTupleBlock places tuple)}
    (hSpos : 0 < μ S)
    (hsub : S ⊆ ((arithmeticTupleSingleFractionalLattice places tuple iSelected t *
      arithmeticTupleHolomorphicLattice places tuple :
        Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
          Set (ArithmeticTensorTupleBlock places tuple))) :
    arithmeticTupleNormalizedLogVolume places tuple μ S ≤
      -(t * Real.log (p : ℝ)) := by
  have hsub' : S ⊆ ((arithmeticTupleFractionalLattice places tuple c *
      arithmeticTupleHolomorphicLattice places tuple :
        Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
          Set (ArithmeticTensorTupleBlock places tuple)) := by
    simpa [hball] using hsub
  have hmain := arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul
    places tuple μ data hSpos hsub'
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast
    (Fact.out : Nat.Prime p).one_lt)
  have hmul : t * Real.log (p : ℝ) ≤ (∑ i, c i) * Real.log (p : ℝ) :=
    mul_le_mul_of_nonneg_right hceiling hlogp.le
  linarith

#print axioms arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
#print axioms arithmeticTupleNormalizedLogVolume_primeScalar_zpow
#print axioms arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul

end

end LeanFormal.IUT.NumberFieldFinitePlace
