/-
# IUT IV Prop 1.5 (i): direct sum versus tensor product metrics on `ℂ ⊗_ℝ ℂ`

Paper (IUT IV L822–845): with `ℂ` carrying its standard Hermitian (real inner product) metric,
the tensor product metric on `ℂ ⊗_ℝ ℂ` and the direct sum metric on `ℂ ⊕ ℂ` correspond, under
the Chinese-remainder ring isomorphism `ℂ ⊗_ℝ ℂ ≅ ℂ ⊕ ℂ`, up to a factor of `2`.

Here the isomorphism is the `ℝ`-algebra map `a ⊗ b ↦ (a b, a b̄)`; the tensor product metric
is Mathlib's inner product on `ℂ ⊗[ℝ] ℂ` (`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ ⟪b, d⟫`), and the direct
sum metric is `⟪(u₁,u₂),(v₁,v₂)⟫ = ⟪u₁,v₁⟫ + ⟪u₂,v₂⟫`.  The identity rests on
`Re(u v) + Re(u v̄) = 2 Re u Re v`.

Scope: proved for the specific isomorphism and then for every `ℝ`-algebra isomorphism
(`complexTensor_algEquiv_inner`): every `ℝ`-algebra automorphism of `ℂ × ℂ` is a component
conjugation/identity possibly composed with the swap, hence an isometry of the direct sum metric.
(A continuous ring isomorphism is `ℝ`-linear, so this covers the paper's "isomorphism of
topological rings": `complexTensor_continuousRingEquiv_inner`.)  Prop 1.5 (ii) is
`complexTensorToProd_map_primitive`; (iii)–(iv) are not treated.
-/

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Instances.RealVectorSpace

open scoped TensorProduct ComplexConjugate

namespace LeanFormal.IUT.IUTIV.Estimates

/-- The Chinese-remainder `ℝ`-algebra map `ℂ ⊗_ℝ ℂ → ℂ × ℂ`, `a ⊗ b ↦ (a b, a b̄)`. -/
noncomputable def complexTensorToProd : ℂ ⊗[ℝ] ℂ →ₐ[ℝ] ℂ × ℂ :=
  Algebra.TensorProduct.lift ((AlgHom.id ℝ ℂ).prod (AlgHom.id ℝ ℂ))
    ((AlgHom.id ℝ ℂ).prod Complex.conjAe.toAlgHom) (fun _ _ => Commute.all _ _)

@[simp] theorem complexTensorToProd_tmul (a b : ℂ) :
    complexTensorToProd (a ⊗ₜ b) = (a * b, a * conj b) := by
  simp [complexTensorToProd]

/-- The direct sum (real) inner product on `ℂ × ℂ`. -/
noncomputable def complexProdInner (u v : ℂ × ℂ) : ℝ :=
  inner ℝ u.1 v.1 + inner ℝ u.2 v.2

/-- `Re(u v) + Re(u v̄) = 2 Re u Re v`, in inner-product form. -/
theorem complexTensorToProd_inner_tmul (a b c d : ℂ) :
    complexProdInner (complexTensorToProd (a ⊗ₜ b)) (complexTensorToProd (c ⊗ₜ d)) =
      2 * inner ℝ (a ⊗ₜ[ℝ] b) (c ⊗ₜ[ℝ] d) := by
  simp only [complexProdInner, complexTensorToProd_tmul, TensorProduct.inner_tmul,
    Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, map_mul]
  ring

/-- **IUT IV Prop 1.5 (i).**  Under `a ⊗ b ↦ (a b, a b̄)`, the direct sum metric is twice the
tensor product metric: `⟪φ x, φ y⟫_⊕ = 2 ⟪x, y⟫_⊗` for all `x y : ℂ ⊗_ℝ ℂ`. -/
theorem complexTensorToProd_inner (x y : ℂ ⊗[ℝ] ℂ) :
    complexProdInner (complexTensorToProd x) (complexTensorToProd y) = 2 * inner ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp [complexProdInner]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp [complexProdInner]
    | tmul c d => exact complexTensorToProd_inner_tmul a b c d
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, complexProdInner, Prod.fst_add, Prod.snd_add, inner_add_right] at h₁ h₂ ⊢
      linarith
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, complexProdInner, Prod.fst_add, Prod.snd_add, inner_add_left] at h₁ h₂ ⊢
    linarith

/-- Length form: `‖(φ x)₁‖² + ‖(φ x)₂‖² = 2 ‖x‖²` (lengths differ by `√2`). -/
theorem complexTensorToProd_norm_sq (x : ℂ ⊗[ℝ] ℂ) :
    ‖(complexTensorToProd x).1‖ ^ 2 + ‖(complexTensorToProd x).2‖ ^ 2 = 2 * ‖x‖ ^ 2 := by
  have h := complexTensorToProd_inner x x
  simp only [complexProdInner, real_inner_self_eq_norm_sq] at h
  rw [h, ← real_inner_self_eq_norm_sq]

/-- The map `a ⊗ b ↦ (a b, a b̄)` is injective (from the metric identity). -/
theorem complexTensorToProd_injective : Function.Injective complexTensorToProd := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := complexTensorToProd_norm_sq x
  rw [hx] at h
  simp only [Prod.fst_zero, Prod.snd_zero, norm_zero] at h
  have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp this

/-- The map `a ⊗ b ↦ (a b, a b̄)` is bijective, hence a ring isomorphism `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ`. -/
theorem complexTensorToProd_bijective : Function.Bijective complexTensorToProd := by
  refine ⟨complexTensorToProd_injective, ?_⟩
  have hdim : Module.finrank ℝ (ℂ ⊗[ℝ] ℂ) = Module.finrank ℝ (ℂ × ℂ) := by
    rw [Module.finrank_tensorProduct, Module.finrank_prod, Complex.finrank_real_complex]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := complexTensorToProd.toLinearMap)).mp complexTensorToProd_injective


/-! ## Every `ℝ`-algebra isomorphism `ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` -/

/-- `ℝ`-algebra endomorphisms of `ℂ` (the identity or conjugation) preserve the real inner
product. -/
theorem inner_complex_algHom (f : ℂ →ₐ[ℝ] ℂ) (z w : ℂ) : inner ℝ (f z) (f w) = inner ℝ z w := by
  rcases Complex.real_algHom_eq_id_or_conj f with rfl | rfl
  · rfl
  · have hc : ∀ z : ℂ, (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) z = conj z := fun _ => rfl
    simp only [hc, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

/-- An idempotent of `ℂ × ℂ` has components in `{0, 1}`. -/
theorem complex_idempotent_eq_zero_or_one {a : ℂ} (h : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- The first-coordinate component of an `ℝ`-algebra endomorphism of `ℂ × ℂ` sending `(1,0)`
to an idempotent `ε`: `z ↦ (σ (z, 0))` read off at the coordinate where `ε` is `1`. -/
noncomputable def complexProdComponentAlgHom (σ : (ℂ × ℂ) →ₐ[ℝ] (ℂ × ℂ)) (i : ℂ × ℂ →ₐ[ℝ] ℂ)
    (h1 : i (σ (1, 0)) = 1) : ℂ →ₐ[ℝ] ℂ where
  toFun z := i (σ (z, 0))
  map_one' := h1
  map_mul' z w := by
    rw [show ((z * w, 0) : ℂ × ℂ) = (z, 0) * (w, 0) by simp, map_mul, map_mul]
  map_zero' := by
    rw [show ((0 : ℂ), (0 : ℂ)) = (0 : ℂ × ℂ) from rfl, map_zero, map_zero]
  map_add' z w := by
    rw [show ((z + w, 0) : ℂ × ℂ) = (z, 0) + (w, 0) by simp, map_add, map_add]
  commutes' r := by
    have : ((algebraMap ℝ ℂ r, 0) : ℂ × ℂ) = r • ((1, 0) : ℂ × ℂ) := by
      ext <;> simp [Algebra.smul_def]
    rw [this, map_smul, map_smul, h1, Algebra.smul_def, mul_one]

/-- The second-coordinate analogue: `z ↦ σ (0, z)`. -/
noncomputable def complexProdComponentAlgHom' (σ : (ℂ × ℂ) →ₐ[ℝ] (ℂ × ℂ)) (i : ℂ × ℂ →ₐ[ℝ] ℂ)
    (h1 : i (σ (0, 1)) = 1) : ℂ →ₐ[ℝ] ℂ where
  toFun z := i (σ (0, z))
  map_one' := h1
  map_mul' z w := by
    rw [show ((0, z * w) : ℂ × ℂ) = (0, z) * (0, w) by simp, map_mul, map_mul]
  map_zero' := by
    rw [show ((0 : ℂ), (0 : ℂ)) = (0 : ℂ × ℂ) from rfl, map_zero, map_zero]
  map_add' z w := by
    rw [show ((0, z + w) : ℂ × ℂ) = (0, z) + (0, w) by simp, map_add, map_add]
  commutes' r := by
    have : ((0, algebraMap ℝ ℂ r) : ℂ × ℂ) = r • ((0, 1) : ℂ × ℂ) := by
      ext <;> simp [Algebra.smul_def]
    rw [this, map_smul, map_smul, h1, Algebra.smul_def, mul_one]

/-- **Every `ℝ`-algebra automorphism of `ℂ × ℂ` preserves the direct sum metric.** -/
theorem complexProdInner_algEquiv (σ : (ℂ × ℂ) ≃ₐ[ℝ] (ℂ × ℂ)) (u v : ℂ × ℂ) :
    complexProdInner (σ u) (σ v) = complexProdInner u v := by
  set e₁ : ℂ × ℂ := (1, 0)
  set e₂ : ℂ × ℂ := (0, 1)
  have he : e₁ + e₂ = 1 := by ext <;> simp [e₁, e₂]
  have hidem : σ e₁ * σ e₁ = σ e₁ := by rw [← map_mul]; congr 1; ext <;> simp [e₁]
  have hne0 : σ e₁ ≠ 0 := fun h => by
    have := σ.injective (h.trans (map_zero σ).symm); simp [e₁, Prod.ext_iff] at this
  have hne1 : σ e₁ ≠ 1 := fun h => by
    have := σ.injective (h.trans (map_one σ).symm); simp [e₁, Prod.ext_iff] at this
  have hσe₂ : σ e₂ = 1 - σ e₁ := by rw [← map_one σ, ← he, map_add]; ring
  have h1 := complex_idempotent_eq_zero_or_one (congrArg Prod.fst hidem)
  have h2 := complex_idempotent_eq_zero_or_one (congrArg Prod.snd hidem)
  -- splitting `u = (u₁, 0) + (0, u₂)`
  have hsplit : ∀ w : ℂ × ℂ, w = (w.1, 0) + (0, w.2) := fun w => by ext <;> simp
  have hz1 : ∀ z : ℂ, σ (z, 0) = σ (z, 0) * σ e₁ := fun z => by
    rw [← map_mul]; congr 1; ext <;> simp [e₁]
  have hz2 : ∀ z : ℂ, σ (0, z) = σ (0, z) * σ e₂ := fun z => by
    rw [← map_mul]; congr 1; ext <;> simp [e₂]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (Prod.ext h1 h2) hne0
  · -- `σ e₁ = (0, 1)`: the swap case
    have hσe₁ : σ e₁ = (0, 1) := Prod.ext h1 h2
    have hσe₂' : σ e₂ = (1, 0) := by rw [hσe₂, hσe₁]; ext <;> simp
    let f := complexProdComponentAlgHom σ.toAlgHom (AlgHom.snd ℝ ℂ ℂ) (by
      change (σ e₁).2 = 1; rw [hσe₁])
    let g := complexProdComponentAlgHom' σ.toAlgHom (AlgHom.fst ℝ ℂ ℂ) (by
      change (σ e₂).1 = 1; rw [hσe₂'])
    have hform : ∀ w : ℂ × ℂ, σ w = (g w.2, f w.1) := fun w => by
      conv_lhs => rw [hsplit w, map_add]
      have a := hz1 w.1
      have b := hz2 w.2
      rw [hσe₁] at a
      rw [hσe₂'] at b
      ext
      · simp only [Prod.fst_add]
        rw [a, b]
        simp [g, complexProdComponentAlgHom']
      · simp only [Prod.snd_add]
        rw [a, b]
        simp [f, complexProdComponentAlgHom]
    simp only [complexProdInner, hform, inner_complex_algHom]
    ring
  · -- `σ e₁ = (1, 0)`: the diagonal case
    have hσe₁ : σ e₁ = (1, 0) := Prod.ext h1 h2
    have hσe₂' : σ e₂ = (0, 1) := by rw [hσe₂, hσe₁]; ext <;> simp
    let f := complexProdComponentAlgHom σ.toAlgHom (AlgHom.fst ℝ ℂ ℂ) (by
      change (σ e₁).1 = 1; rw [hσe₁])
    let g := complexProdComponentAlgHom' σ.toAlgHom (AlgHom.snd ℝ ℂ ℂ) (by
      change (σ e₂).2 = 1; rw [hσe₂'])
    have hform : ∀ w : ℂ × ℂ, σ w = (f w.1, g w.2) := fun w => by
      conv_lhs => rw [hsplit w, map_add]
      have a := hz1 w.1
      have b := hz2 w.2
      rw [hσe₁] at a
      rw [hσe₂'] at b
      ext
      · simp only [Prod.fst_add]
        rw [a, b]
        simp [f, complexProdComponentAlgHom]
      · simp only [Prod.snd_add]
        rw [a, b]
        simp [g, complexProdComponentAlgHom']
    simp only [complexProdInner, hform, inner_complex_algHom]
  · exact absurd (Prod.ext h1 h2) hne1

/-- **IUT IV Prop 1.5 (i), for every `ℝ`-algebra isomorphism.**  For any `ℝ`-algebra
isomorphism `ψ : ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ`, the direct sum metric is twice the tensor product metric. -/
theorem complexTensor_algEquiv_inner (ψ : ℂ ⊗[ℝ] ℂ ≃ₐ[ℝ] (ℂ × ℂ)) (x y : ℂ ⊗[ℝ] ℂ) :
    complexProdInner (ψ x) (ψ y) = 2 * inner ℝ x y := by
  let φ : ℂ ⊗[ℝ] ℂ ≃ₐ[ℝ] (ℂ × ℂ) := AlgEquiv.ofBijective complexTensorToProd
    complexTensorToProd_bijective
  let σ : (ℂ × ℂ) ≃ₐ[ℝ] (ℂ × ℂ) := φ.symm.trans ψ
  have hψ : ∀ z, ψ z = σ (complexTensorToProd z) := fun z => by
    simp [σ, φ]
  rw [hψ, hψ, complexProdInner_algEquiv, complexTensorToProd_inner]


/-! ## Prop 1.5 (ii): primitive automorphisms preserve the decomposition -/

/-- The primitive automorphisms of `ℂ` (IV L826–829): the group of order `8` generated by
complex conjugation and multiplication by `±1`, `±i`, i.e. `z ↦ u z` or `z ↦ u z̄` with
`u ∈ {1, -1, i, -i}`. -/
def IsPrimitiveComplexAut (α : ℂ →ₗ[ℝ] ℂ) : Prop :=
  ∃ u : ℂ, (u = 1 ∨ u = -1 ∨ u = Complex.I ∨ u = -Complex.I) ∧
    ((∀ z, α z = u * z) ∨ (∀ z, α z = u * conj z))

theorem conj_mul_self_eq_one_of_primitiveUnit {u : ℂ}
    (hu : u = 1 ∨ u = -1 ∨ u = Complex.I ∨ u = -Complex.I) : conj u * u = 1 := by
  rcases hu with rfl | rfl | rfl | rfl <;> simp

/-- Multiplication by a unit-modulus scalar, optionally after conjugation, is an isometry of
the real inner product on `ℂ`. -/
theorem inner_unitMul_conjOpt (w : ℂ) (hw : conj w * w = 1) (c : Bool) (z z' : ℂ) :
    inner ℝ (w * (if c then conj z else z)) (w * (if c then conj z' else z')) =
      inner ℝ z z' := by
  have hw' : w.re * w.re + w.im * w.im = 1 := by
    have := congrArg Complex.re hw
    simpa [Complex.mul_re, Complex.conj_re, Complex.conj_im] using this
  cases c <;>
  · simp only [Complex.inner, Bool.false_eq_true, if_false, if_true, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, map_mul]
    linear_combination (z.re * z'.re + z.im * z'.im) * hw'

/-- **IUT IV Prop 1.5 (ii).**  For primitive automorphisms `α`, `β` of the two factors, the
induced automorphism `α ⊗ β` of `ℂ ⊗_ℝ ℂ` corresponds, under `a ⊗ b ↦ (a b, a b̄)`, to a map
of `ℂ × ℂ` that either preserves or swaps the two summands and acts on each by
`x ↦ w x` or `x ↦ w x̄` with `|w| = 1`; in particular it preserves the direct sum
decomposition and the direct sum metric. -/
theorem complexTensorToProd_map_primitive (α β : ℂ →ₗ[ℝ] ℂ)
    (hα : IsPrimitiveComplexAut α) (hβ : IsPrimitiveComplexAut β) :
    ∃ (sw c : Bool) (w₁ w₂ : ℂ), conj w₁ * w₁ = 1 ∧ conj w₂ * w₂ = 1 ∧
      ∀ x : ℂ ⊗[ℝ] ℂ,
        let y := complexTensorToProd x
        let y' := if sw then (y.2, y.1) else y
        complexTensorToProd (TensorProduct.map α β x) =
          (w₁ * (if c then conj y'.1 else y'.1), w₂ * (if c then conj y'.2 else y'.2)) := by
  obtain ⟨u, hu, hαf⟩ := hα
  obtain ⟨v, hv, hβf⟩ := hβ
  have hu1 := conj_mul_self_eq_one_of_primitiveUnit hu
  have hv1 := conj_mul_self_eq_one_of_primitiveUnit hv
  have hw : ∀ a b : ℂ, conj a * a = 1 → conj b * b = 1 → conj (a * b) * (a * b) = 1 :=
    fun a b ha hb => by
      rw [map_mul, show conj a * conj b * (a * b) = (conj a * a) * (conj b * b) by ring, ha, hb,
        one_mul]
  have hw' : ∀ a b : ℂ, conj a * a = 1 → conj b * b = 1 →
      conj (a * conj b) * (a * conj b) = 1 := fun a b ha hb => by
    rw [map_mul, Complex.conj_conj, show conj a * b * (a * conj b) = (conj a * a) * (conj b * b)
      by ring, ha, hb, one_mul]
  -- the four shapes; the identity is additive in `x`, so it suffices on pure tensors
  have key : ∀ (sw c : Bool) (w₁ w₂ : ℂ),
      (∀ a b : ℂ, complexTensorToProd (TensorProduct.map α β (a ⊗ₜ b)) =
        (let y := complexTensorToProd (a ⊗ₜ b)
         let y' := if sw then (y.2, y.1) else y
         (w₁ * (if c then conj y'.1 else y'.1), w₂ * (if c then conj y'.2 else y'.2)))) →
      ∀ x : ℂ ⊗[ℝ] ℂ,
        complexTensorToProd (TensorProduct.map α β x) =
          (let y := complexTensorToProd x
           let y' := if sw then (y.2, y.1) else y
           (w₁ * (if c then conj y'.1 else y'.1), w₂ * (if c then conj y'.2 else y'.2))) := by
    intro sw c w₁ w₂ h x
    induction x using TensorProduct.induction_on with
    | zero => cases sw <;> cases c <;> simp <;> rfl
    | tmul a b => exact h a b
    | add x₁ x₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂, map_add]
      cases sw <;> cases c <;> ext <;> simp <;> ring
  rcases hαf with hαf | hαf <;> rcases hβf with hβf | hβf
  · refine ⟨false, false, u * v, u * conj v, hw u v hu1 hv1, hw' u v hu1 hv1, key _ _ _ _ ?_⟩
    intro a b
    simp [hαf, hβf]
    constructor <;> ring
  · refine ⟨true, false, u * v, u * conj v, hw u v hu1 hv1, hw' u v hu1 hv1, key _ _ _ _ ?_⟩
    intro a b
    simp [hαf, hβf]
    constructor <;> ring
  · refine ⟨true, true, u * v, u * conj v, hw u v hu1 hv1, hw' u v hu1 hv1, key _ _ _ _ ?_⟩
    intro a b
    simp [hαf, hβf]
    constructor <;> ring
  · refine ⟨false, true, u * v, u * conj v, hw u v hu1 hv1, hw' u v hu1 hv1, key _ _ _ _ ?_⟩
    intro a b
    simp [hαf, hβf]
    constructor <;> ring


/-- **IUT IV Prop 1.5 (i), for every isomorphism of topological rings.**  A continuous ring
isomorphism `ψ : ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ` is automatically `ℝ`-linear (`map_real_smul`), hence an
`ℝ`-algebra isomorphism, and the direct sum metric is twice the tensor product metric. -/
theorem complexTensor_continuousRingEquiv_inner (ψ : ℂ ⊗[ℝ] ℂ ≃+* (ℂ × ℂ)) (hψ : Continuous ψ)
    (x y : ℂ ⊗[ℝ] ℂ) :
    complexProdInner (ψ x) (ψ y) = 2 * inner ℝ x y := by
  have hsmul : ∀ (r : ℝ) (z : ℂ ⊗[ℝ] ℂ), ψ (r • z) = r • ψ z := fun r z =>
    map_real_smul ψ hψ r z
  let ψ' : ℂ ⊗[ℝ] ℂ ≃ₐ[ℝ] (ℂ × ℂ) := AlgEquiv.ofRingEquiv (f := ψ) (fun r => by
    rw [Algebra.algebraMap_eq_smul_one, hsmul, map_one, ← Algebra.algebraMap_eq_smul_one])
  exact complexTensor_algEquiv_inner ψ' x y

end LeanFormal.IUT.IUTIV.Estimates
