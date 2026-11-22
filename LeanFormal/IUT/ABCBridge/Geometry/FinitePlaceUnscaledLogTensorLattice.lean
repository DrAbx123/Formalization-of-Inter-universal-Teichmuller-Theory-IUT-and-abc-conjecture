import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralLogTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexResidueFormula

/-!
# The actual unscaled unit-log tensor at a tuple of finite places

The arithmetic integral log tensor `arithmeticTupleIntegralLogLattice` is the
`Zp`-span of the scaled local shells `(p*)^{-1} log(O^×)`.  This file forms
the honest tensor of the unscaled local images `log(O^×)`.

The local unscaled lattice is `p* • I` in each tensor factor.  After taking
the tensor product over `Qp` the common scalar is therefore raised to the
number of tensor factors:
`arithmeticTupleUnitLogLattice = (p*)^(Fintype.card ι) • I_tensor`.
The single-factor case, which is the form used when the tuple has one entry,
is recorded separately below.  This is not the canonical holomorphic unit
region; it is the log-volume carrier used in Step (v) / Proposition 1.4(iii).
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.LocalFieldLogarithm MeasureTheory
open scoped LeanFormal.IUT.FinitePadicIntegralLattice Pointwise

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

section LocalScaling

variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L]

/-- The local unscaled unit-log lattice is the scaled integral log-shell,
with the paper's scalar `p*` viewed as a `Qp`-scalar. -/
theorem unitLogLattice_eq_padicScalar_smul_integralLogShellLattice :
    unitLogLattice (K := L) (p := p) =
      (logShellScale p : ℚ_[p]) • integralLogShellLattice (K := L) (p := p) := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists]
  change (∃ y ∈ (integralLogShellLattice (K := L) (p := p) : Set L),
      (logShellScale p : L) * y = x) ↔
    ∃ b ∈ (integralLogShellLattice (K := L) (p := p) : Set L),
      (logShellScale p : ℚ_[p]) • b = x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    calc (logShellScale p : ℚ_[p]) • y
        = (logShellScale p : L) * y := by
          rw [Algebra.smul_def (R := ℚ_[p]) (A := L)]
          simp
      _ = x := hxy
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    calc (logShellScale p : L) * y
        = (logShellScale p : ℚ_[p]) • y := by
          rw [Algebra.smul_def (R := ℚ_[p]) (A := L)]
          simp
      _ = x := hxy

omit [CharZero L] [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L] in
/-- A nonzero `Qp`-scalar does not change the rational span of a `Qp`-submodule. -/
theorem padicScalar_smul_top_eq_top {M : Type*} [AddCommGroup M] [Module ℚ_[p] M]
    {c : ℚ_[p]} (hc : c ≠ 0) :
    c • (⊤ : Submodule ℚ_[p] M) = ⊤ := by
  apply top_unique
  intro x _
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨c⁻¹ • x, trivial, ?_⟩
  change c • (c⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem span_padic_unitLogLattice_eq_top [FiniteDimensional ℚ_[p] L] :
    Submodule.span ℚ_[p] (unitLogLattice (K := L) (p := p) : Set L) = ⊤ := by
  have hset : (unitLogLattice (K := L) (p := p) : Set L) =
      (logShellScale p : ℚ_[p]) •
        (integralLogShellLattice (K := L) (p := p) : Set L) := by
    rw [unitLogLattice_eq_padicScalar_smul_integralLogShellLattice,
      Submodule.coe_pointwise_smul]
  rw [hset, Submodule.span_smul, span_padic_integralLogShellLattice_eq_top]
  exact padicScalar_smul_top_eq_top (p := p)
    (Nat.cast_ne_zero.mpr (ne_of_gt (logShellScale_pos (p := p))))

end LocalScaling

section TwoInvUnit

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℚ_[p] M]

/-- For odd `p` the rational `2` is a unit of `Zp`: its inverse has norm one, so
every inverse power of `2` acts as an automorphism of an integral submodule. -/
theorem twoInvPow_smul_eq_self (hp : p ≠ 2) (n : ℕ) (S : Submodule ℤ_[p] M) :
    (((2 : ℚ_[p]) ^ n)⁻¹) • S = S := by
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes Fact.out Nat.prime_two).mpr hp
  have h2norm : ‖(2 : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  let z : ℤ_[p] := ⟨(2 : ℚ_[p])⁻¹, by rw [norm_inv, h2norm, inv_one]⟩
  have hz : (z : ℚ_[p]) = (2 : ℚ_[p])⁻¹ := rfl
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hb : ((2 : ℚ_[p]) ^ n)⁻¹ = ((z ^ n : ℤ_[p]) : ℚ_[p]) := by
      rw [PadicInt.coe_pow, hz, inv_pow]
    rw [hb, ← LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq (p := p) (z ^ n) y]
    exact S.smul_mem (z ^ n) hy
  · intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨((2 : ℚ_[p]) ^ n) • x, ?_, ?_⟩
    · let z2 : ℤ_[p] := ⟨(2 : ℚ_[p]), by rw [h2norm]⟩
      have hz2 : (z2 : ℚ_[p]) = (2 : ℚ_[p]) := rfl
      have h2 : (2 : ℚ_[p]) ^ n = ((z2 ^ n : ℤ_[p]) : ℚ_[p]) := by
        rw [PadicInt.coe_pow, hz2]
      rw [h2, ← LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq (p := p)
        (z2 ^ n) x]
      exact S.smul_mem _ hx
    · exact inv_smul_smul₀ (pow_ne_zero _ (by norm_num)) x



end TwoInvUnit
section TensorScaling

variable {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable (S : (i : ι) → Submodule ℤ_[p] (M i))

omit [∀ i, FiniteDimensional ℚ_[p] (M i)] in
/-- Scaling every local submodule by the same `Qp`-scalar scales the pure
tensor region by the product of the scalars, i.e. by its `Fintype.card ι`-th
power. -/
theorem tensorIntegralRegion_const_smul (c : ℚ_[p]) :
    tensorIntegralRegion (p := p) M
        (fun i => c • (S i : Set (M i))) =
      c ^ Fintype.card ι •
        tensorIntegralRegion (p := p) M (fun i => (S i : Set (M i))) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    choose y hy hxy using fun i =>
      Set.mem_smul_set.mp (hx i (Set.mem_univ i))
    refine Set.mem_smul_set.mpr
      ⟨finitePadicTensorTprod (p := p) M y,
        ⟨y, fun i _ => hy i, rfl⟩, ?_⟩
    rw [show finitePadicTensorTprod (p := p) M x =
        finitePadicTensorTprod (p := p) M (fun i => c • y i) by
      congr 1
      funext i
      exact (hxy i).symm]
    rw [(finitePadicTensorTprod (p := p) M).map_smul_univ (fun _ => c) y]
    congr 1
    simp [Finset.prod_const]
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    refine ⟨fun i => c • y i,
      fun i _ => Set.smul_mem_smul_set (hy i (Set.mem_univ i)), ?_⟩
    rw [(finitePadicTensorTprod (p := p) M).map_smul_univ (fun _ => c) y]
    congr 1
    simp [Finset.prod_const]

/-- The `Zp`-span of the scaled pure-tensor region is the corresponding
power of the original tensor span. -/
theorem submoduleTensorSpan_const_smul (c : ℚ_[p]) :
    submoduleTensorSpan (p := p) M (fun i => c • S i) =
      c ^ Fintype.card ι • submoduleTensorSpan (p := p) M S := by
  unfold submoduleTensorSpan
  change Submodule.span ℤ_[p]
      (tensorIntegralRegion (p := p) M (fun i => c • (S i : Set (M i)))) =
    c ^ Fintype.card ι • Submodule.span ℤ_[p]
      (tensorIntegralRegion (p := p) M (fun i => (S i : Set (M i))))
  rw [tensorIntegralRegion_const_smul]
  exact Submodule.span_smul (R := ℤ_[p])
    (M := FinitePadicTensor (p := p) M) (c ^ Fintype.card ι)
    (tensorIntegralRegion (p := p) M (fun i => (S i : Set (M i))))

end TensorScaling

abbrev arithmeticTupleLocalUnscaledUnitLogLattice :
    (i : ι) → Submodule ℤ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
  fun i => unitLogLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p)

/-- The actual unscaled unit-log tensor lattice: the `Zp`-span of pure tensors
of the local unscaled images `Set.range unitLog`. -/
abbrev arithmeticTupleUnitLogLattice :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  submoduleTensorSpan (p := p)
    (fun i => CommonPrimeCompletion (places i (tuple i)))
    (arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple)

/-- The existing arithmetic log tensor is the same submodule span as the
`submoduleTensorSpan` of the individual scaled log-shell lattices. -/
theorem arithmeticTupleIntegralLogLattice_eq_submoduleTensorSpan :
    arithmeticTupleIntegralLogLattice places tuple =
      submoduleTensorSpan (p := p)
        (fun i => CommonPrimeCompletion (places i (tuple i)))
        (fun i => integralLogShellLattice (K := CommonPrimeCompletion (places i (tuple i)))
          (p := p)) := rfl

/-- The actual tensor of the unscaled local unit-log images is the
`(p*)^(Fintype.card ι)`-multiple of the scaled integral log tensor.  The
exponent records the number of tensor factors; it is not silently set to one. -/
theorem arithmeticTupleUnitLogLattice_eq_scale_smul_integralLogLattice :
    arithmeticTupleUnitLogLattice places tuple =
      ((logShellScale p : ℚ_[p]) ^ Fintype.card ι) •
        arithmeticTupleIntegralLogLattice places tuple := by
  rw [arithmeticTupleUnitLogLattice]
  have hlocal : arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple =
      fun i => (logShellScale p : ℚ_[p]) •
        integralLogShellLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p) := by
    funext i
    exact unitLogLattice_eq_padicScalar_smul_integralLogShellLattice
      (L := CommonPrimeCompletion (places i (tuple i))) (p := p)
  rw [hlocal]
  rw [submoduleTensorSpan_const_smul (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := fun i => integralLogShellLattice (K := CommonPrimeCompletion (places i (tuple i)))
      (p := p))
    ((logShellScale p : ℚ_[p]))]
  rw [← arithmeticTupleIntegralLogLattice_eq_submoduleTensorSpan]

/-- In the one-factor case the scalar is exactly the paper's `p*`. -/
theorem arithmeticTupleUnitLogLattice_eq_scale_smul_integralLogLattice_of_card_eq_one
    (hι : Fintype.card ι = 1) :
    arithmeticTupleUnitLogLattice places tuple =
      (logShellScale p : ℚ_[p]) • arithmeticTupleIntegralLogLattice places tuple := by
  rw [arithmeticTupleUnitLogLattice_eq_scale_smul_integralLogLattice, hι, pow_one]

/-- The unscaled unit-log tensor is contained in the scaled integral log
tensor, because `p*` is an integral `Zp`-scalar.  At `p = 2` this is the
scalar `p^2`, not `p`. -/
theorem arithmeticTupleUnitLogLattice_le_integralLogLattice :
    arithmeticTupleUnitLogLattice places tuple ≤
      arithmeticTupleIntegralLogLattice places tuple := by
  rw [arithmeticTupleUnitLogLattice_eq_scale_smul_integralLogLattice]
  intro x hx
  rw [Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  let z : ℤ_[p] := (logShellScale p : ℤ_[p])
  have hpow : ((z ^ Fintype.card ι : ℤ_[p]) : ℚ_[p]) =
      (logShellScale p : ℚ_[p]) ^ Fintype.card ι := by
    rw [PadicInt.coe_pow]
    simp [z]
  rw [← hpow]
  simpa only [LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq] using
    (arithmeticTupleIntegralLogLattice places tuple).smul_mem (z ^ Fintype.card ι) hy

/-- The intermediate Step (v) container identity.  Multiplying the unscaled
tensor `U = (p*)^|I| • I_tensor` by `p^(floor lam - |I|) * 2^(-|I|)` gives the
half-open container `p^(floor lam) • I_tensor`.  At odd `p` the factor
`2^(-|I|)` is a `Zp`-unit and hence acts trivially on `I_tensor`; at `p = 2` it
cancels the extra factor `p^|I|` in `logShellScale 2 = 2^2`.  This is a
container bookkeeping identity only; it does not identify `U` with the N4/N6
unit region. -/
theorem padicPow_smul_twoInvPow_smul_arithmeticTupleUnitLogLattice
    (lam : ℝ) (hlam : Fintype.card ι ≤ ⌊lam⌋₊) :
    (p : ℚ_[p]) ^ (⌊lam⌋₊ - Fintype.card ι) •
        ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹ •
        arithmeticTupleUnitLogLattice places tuple =
      (p : ℚ_[p]) ^ ⌊lam⌋₊ • arithmeticTupleIntegralLogLattice places tuple := by
  rw [arithmeticTupleUnitLogLattice_eq_scale_smul_integralLogLattice]
  rw [logShellScale_eq_prime_pow_factor, Nat.cast_pow, ← pow_mul]
  rw [smul_smul, smul_smul]
  rcases eq_or_ne p 2 with hp | hp
  · subst hp
    have hs2 : logShellScaleExponentFactor (p := 2) = 2 := by
      simp [logShellScaleExponentFactor]
    rw [hs2]
    congr 1
    have h2n : (2 : ℚ_[2]) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2nn : (2 : ℚ_[2]) ^ (2 * Fintype.card ι) =
        (2 : ℚ_[2]) ^ Fintype.card ι * (2 : ℚ_[2]) ^ Fintype.card ι := by
      rw [two_mul, pow_add]
    have hb2 : ((2 : ℚ_[2]) ^ Fintype.card ι)⁻¹ *
        ((2 : ℚ_[2]) ^ Fintype.card ι * (2 : ℚ_[2]) ^ Fintype.card ι) =
        (2 : ℚ_[2]) ^ Fintype.card ι := by
      rw [← mul_assoc, inv_mul_cancel₀ h2n, one_mul]
    calc ((2 : ℚ_[2]) ^ (⌊lam⌋₊ - Fintype.card ι) * ((2 : ℚ_[2]) ^ Fintype.card ι)⁻¹) *
          (2 : ℚ_[2]) ^ (2 * Fintype.card ι)
        = (2 : ℚ_[2]) ^ (⌊lam⌋₊ - Fintype.card ι) *
            (((2 : ℚ_[2]) ^ Fintype.card ι)⁻¹ *
              ((2 : ℚ_[2]) ^ Fintype.card ι * (2 : ℚ_[2]) ^ Fintype.card ι)) := by
          rw [h2nn]
          ring
      _ = (2 : ℚ_[2]) ^ (⌊lam⌋₊ - Fintype.card ι) * (2 : ℚ_[2]) ^ Fintype.card ι := by
          rw [hb2]
      _ = (2 : ℚ_[2]) ^ ⌊lam⌋₊ := by
          rw [← pow_add, Nat.sub_add_cancel hlam]
  · have hs1 : logShellScaleExponentFactor (p := p) = 1 := by
      simp [logShellScaleExponentFactor, hp]
    rw [hs1, one_mul]
    have hpow : (p : ℚ_[p]) ^ (⌊lam⌋₊ - Fintype.card ι) * (p : ℚ_[p]) ^ Fintype.card ι =
        (p : ℚ_[p]) ^ ⌊lam⌋₊ := by
      rw [← pow_add, Nat.sub_add_cancel hlam]
    have hscalar :
        ((p : ℚ_[p]) ^ (⌊lam⌋₊ - Fintype.card ι) * ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹) *
            (p : ℚ_[p]) ^ Fintype.card ι =
          (p : ℚ_[p]) ^ ⌊lam⌋₊ * ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹ := by
      calc
        ((p : ℚ_[p]) ^ (⌊lam⌋₊ - Fintype.card ι) * ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹) *
            (p : ℚ_[p]) ^ Fintype.card ι
            = ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹ *
                ((p : ℚ_[p]) ^ (⌊lam⌋₊ - Fintype.card ι) *
                  (p : ℚ_[p]) ^ Fintype.card ι) := by ring
        _ = ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹ * (p : ℚ_[p]) ^ ⌊lam⌋₊ := by rw [hpow]
        _ = (p : ℚ_[p]) ^ ⌊lam⌋₊ * ((2 : ℚ_[p]) ^ Fintype.card ι)⁻¹ := by ring
    rw [hscalar]
    rw [← smul_smul, twoInvPow_smul_eq_self (p := p) hp]


instance arithmeticTupleUnitLogLatticeFinite :
    Module.Finite ℤ_[p] (arithmeticTupleUnitLogLattice places tuple) :=
  finite_submoduleTensorSpan (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple)
    (fun i => isCompact_unitLogLattice (K := CommonPrimeCompletion (places i (tuple i)))
      (p := p))

instance arithmeticTupleUnitLogLatticeFree :
    Module.Free ℤ_[p] (arithmeticTupleUnitLogLattice places tuple) :=
  free_submoduleTensorSpan (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple)
    (fun i => isCompact_unitLogLattice (K := CommonPrimeCompletion (places i (tuple i)))
      (p := p))

theorem isCompact_arithmeticTupleUnitLogLattice :
    IsCompact (arithmeticTupleUnitLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) :=
  isCompact_submoduleTensorSpan (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple)
    (fun i => isCompact_unitLogLattice (K := CommonPrimeCompletion (places i (tuple i)))
      (p := p))

theorem isOpen_arithmeticTupleUnitLogLattice :
    IsOpen (arithmeticTupleUnitLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) := by
  letI : ∀ i, Module.Finite ℤ_[p]
      (arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple i) :=
    fun i => unitLogLatticeFinite (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  apply isOpen_submoduleTensorSpan (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple)
  intro i
  exact span_padic_unitLogLattice_eq_top
    (L := CommonPrimeCompletion (places i (tuple i))) (p := p)

theorem span_padic_arithmeticTupleUnitLogLattice :
    Submodule.span ℚ_[p] (arithmeticTupleUnitLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) = ⊤ := by
  letI : ∀ i, Module.Free ℤ_[p]
      (arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple i) :=
    fun i => unitLogLatticeFree (K := CommonPrimeCompletion (places i (tuple i))) (p := p)
  exact padic_span_submoduleTensorSpan_eq_top (p := p)
    (M := fun i => CommonPrimeCompletion (places i (tuple i)))
    (S := arithmeticTupleLocalUnscaledUnitLogLattice (p := p) places tuple)
    (fun i => span_padic_unitLogLattice_eq_top
      (L := CommonPrimeCompletion (places i (tuple i))) (p := p))

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]

theorem measure_arithmeticTupleUnitLogLattice_pos_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    0 < μ (arithmeticTupleUnitLogLattice places tuple : Set _) ∧
      μ (arithmeticTupleUnitLogLattice places tuple : Set _) < ⊤ := by
  have hopen := isOpen_arithmeticTupleUnitLogLattice places tuple
  exact ⟨Measure.measure_pos_of_nonempty_interior μ
    (by rw [hopen.interior_eq]; exact ⟨0, Submodule.zero_mem _⟩),
    (isCompact_arithmeticTupleUnitLogLattice places tuple).measure_lt_top⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace
