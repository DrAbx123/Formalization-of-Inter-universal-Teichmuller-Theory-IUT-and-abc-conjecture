import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Rational saturation of local integral structures and their true tensor packets

Prerequisite for IUT III Proposition 3.2(ii) and N4--N7. The tensor base is
the local field `k`, whereas the integral structure is rationalized over `Q`.
These two scalar operations are deliberately kept separate.

The first theorem proves rational saturation of the closed unit ball whenever
a nonzero rational integer is strictly contracting. The last theorem combines
this with genuine `PiTensorProduct` algebra. It neither multiplies all tensor
factors into one field nor presupposes an unproved source carrier interface.

The source log-shell identification with an integral lattice, tensor packet
field decomposition and source topology still have to be constructed.
-/

open Filter Metric
open scoped Topology TensorProduct

namespace LeanFormal.IUT.LocalFieldIntegralTensorSpan

/-- Multiplying by a sufficiently high power of a strictly contracting
rational integer moves any field element into the integral unit ball. -/
theorem exists_integer_pow_mul_mem_unitBall {K : Type*} [NormedField K]
    (p : ℕ) (hp : ‖(p : K)‖ < 1) (x : K) :
    ∃ n : ℕ, ‖(p : K) ^ n * x‖ ≤ 1 := by
  have ht : Tendsto (fun n : ℕ => (p : K) ^ n * x) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp).mul_const x
  obtain ⟨n, hn⟩ := (ht.eventually (ball_mem_nhds (0 : K) zero_lt_one)).exists
  exact ⟨n, (by simpa only [mem_ball, dist_zero_right] using hn :
    ‖(p : K) ^ n * x‖ < 1).le⟩

/-- The rational span of the local integral structure is the whole field.
This is an actual saturation proof, not an extra interface field. -/
theorem rat_span_unitBall_eq_top {K : Type*} [NormedField K] [CharZero K]
    (p : ℕ) (hp0 : p ≠ 0) (hp : ‖(p : K)‖ < 1) :
    Submodule.span ℚ (closedBall (0 : K) 1) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨n, hn⟩ := exists_integer_pow_mul_mem_unitBall p hp x
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hmem : (p : K) ^ n * x ∈ Submodule.span ℚ (closedBall (0 : K) 1) :=
    Submodule.subset_span (by simpa only [mem_closedBall, dist_zero_right] using hn)
  have hscale := Submodule.smul_mem (Submodule.span ℚ (closedBall (0 : K) 1))
    (((p : ℚ) ^ n)⁻¹) hmem
  simpa [Rat.smul_def, hpK] using hscale

/-- The contraction hypothesis is automatic in the actual base local field. -/
theorem padic_rat_span_unitBall_eq_top (p : ℕ) [Fact p.Prime] :
    Submodule.span ℚ (closedBall (0 : ℚ_[p]) 1) = ⊤ := by
  apply rat_span_unitBall_eq_top p (Fact.out : Nat.Prime p).ne_zero
  rw [Padic.norm_p]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact inv_lt_one_of_one_lt₀ hp

section Multilinear

variable {ι : Type*} [Finite ι] {M : ι → Type*} {N : Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)] [AddCommGroup N] [Module ℚ N]

/-- A multilinear map is generated rationally by the images of any
coordinatewise rational generating sets. -/
theorem multilinear_mem_span_integralImages (S : (i : ι) → Set (M i))
    (hS : ∀ i, Submodule.span ℚ (S i) = ⊤) (f : MultilinearMap ℚ M N)
    (x : (i : ι) → M i) :
    f x ∈ Submodule.span ℚ (Set.range
      (fun y : (i : ι) → S i => f (fun i => (y i).val))) := by
  let P := Submodule.span ℚ (Set.range
    (fun y : (i : ι) → S i => f (fun i => (y i).val)))
  have hgenerators : ∀ i, Submodule.span ℚ
      (Set.range (fun y : S i => (y : M i))) = ⊤ := by
    intro i
    have heq : Set.range (fun y : S i => (y : M i)) = S i := by
      ext y
      exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
    rw [heq]
    exact hS i
  have hzero : P.mkQ.compMultilinearMap f = 0 := by
    apply MultilinearMap.ext_of_span_eq_top hgenerators
    intro y
    change P.mkQ (f (fun i => (y i).val)) = 0
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using
      (show f (fun i => (y i).val) ∈ P from Submodule.subset_span ⟨y, rfl⟩)
  have hx : P.mkQ (f x) = 0 := DFunLike.congr_fun hzero x
  simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx

end Multilinear

section LocalTensor

variable {k : Type*} [Field k] [CharZero k]
    {ι : Type*} [Finite ι] [Nonempty ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]
    [∀ i, Module ℚ (M i)] [∀ i, IsScalarTower ℚ k (M i)]

/-- The tensor product is over the local field, and the span is over the
rationals. Nonemptiness matters: the empty tensor is `k`, not `Q`. -/
theorem rat_span_integralTensors_eq_top (S : (i : ι) → Set (M i))
    (hS : ∀ i, Submodule.span ℚ (S i) = ⊤) :
    Submodule.span ℚ (Set.range (fun x : (i : ι) → S i =>
      PiTensorProduct.tprod k (fun i => (x i).val))) =
      (⊤ : Submodule ℚ (⨂[k] i, M i)) := by
  classical
  let P := Submodule.span ℚ (Set.range (fun x : (i : ι) → S i =>
    PiTensorProduct.tprod k (fun i => (x i).val)))
  have hpure : ∀ x : (i : ι) → M i, PiTensorProduct.tprod k x ∈ P :=
    fun x => multilinear_mem_span_integralImages S hS
      ((PiTensorProduct.tprod k).restrictScalars ℚ) x
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      let i : ι := Classical.choice ‹Nonempty ι›
      have heq : PiTensorProduct.tprod k (Function.update x i (r • x i)) =
          r • PiTensorProduct.tprod k x := by
        simpa only [Function.update_eq_self] using
          (PiTensorProduct.tprod k).map_update_smul x i r (x i)
      rw [← heq]
      exact hpure _
  | add x y hx hy => exact Submodule.add_mem P hx hy

end LocalTensor

/-- Combination for actual normed field factors: rational saturation of each
integer ball gives rational saturation of the genuine local-base tensor.
The norms may come from distinct finite extensions of `k`. -/
theorem rat_span_unitBallTensors_eq_top {k : Type*} [Field k] [CharZero k]
    {ι : Type*} [Finite ι] [Nonempty ι] {K : ι → Type*}
    [∀ i, NormedField (K i)] [∀ i, CharZero (K i)]
    [∀ i, Module k (K i)] [∀ i, IsScalarTower ℚ k (K i)]
    (p : ℕ) (hp0 : p ≠ 0) (hp : ∀ i, ‖(p : K i)‖ < 1) :
    Submodule.span ℚ (Set.range
      (fun x : (i : ι) → closedBall (0 : K i) 1 =>
        PiTensorProduct.tprod k (fun i => (x i).val))) =
      (⊤ : Submodule ℚ (⨂[k] i, K i)) :=
  rat_span_integralTensors_eq_top _ (fun i => rat_span_unitBall_eq_top p hp0 (hp i))

end LeanFormal.IUT.LocalFieldIntegralTensorSpan
