/-
# IUT IV Prop 1.5 (iii)–(iv): tensor products of several copies of `⊕_V ℂ`

Paper (IUT IV L846–885).  Let `I`, `V` be nonempty finite sets, `M = ⊕_{v ∈ V} ℂ_v` with the
direct sum metric, and `M_I = ⊗_{i ∈ I} M_i` (tensor product over `ℝ`) with the tensor product
metric.  The ring structure decomposes `M_I` as a direct sum of `2^{|I|-1} · |V|^{|I|}` copies of
`ℂ`, whose direct sum metric is `2^{|I|-1}` times the tensor product metric; and
`⊗ m_i ∈ λ^{|I|} · B_I` when every component of every `m_i` has length `λ`.

Formalization.  `M := V → ℂ`; the tensor product metric on `⨂[ℝ] _ : I, M` is the bilinear
form `tensorMetric` with `tensorMetric (⊗ a) (⊗ b) = ∏ i ⟪a i, b i⟫_M` (built from Mathlib's
`PiTensorProduct.dualDistrib`).  The decomposition is the explicit `ℝ`-algebra map
`characterMap : M_I → (J → ℂ)`, `J = (I → V) × ({i // i ≠ i₀} → Bool)`,
`(⊗ m)_{(v, σ)} = m_{i₀}(v i₀) · ∏_{i ≠ i₀} σ_i(m_i (v i))` with `σ_i ∈ {id, conj}`; so
`|J| = |V|^{|I|} · 2^{|I|-1}`.  The metric identity rests on `∑_σ ∏ σ_i(z_i) = ∏ (z_i + z̄_i)`.

Proved: `characterMap_inner` (direct sum metric = `2^{|I|-1}` × tensor metric),
`characterMap_bijective` (the algebra map is an isomorphism onto `∏_J ℂ`, via positive
definiteness `tensorMetric_self` in the product basis `{δ_v, i δ_v}^{⊗I}` and a dimension
count), `card_characterIndex`, and (iv) `characterMap_tprod_norm` /
`characterMap_tprod_mem_scaled_unitBall`; the last sentence of (iii), invariance under
automorphisms induced by primitive automorphisms of the summands `ℂ_v` of the factors:
`characterMap_map_primitive` (coordinates permuted by `primitivePerm`, up to units and
conjugation), `directSumInner_map_primitive`, `tensorMetric_map_primitive`,
`characterMap_coord_norm_map_primitive` (so `B_I` is preserved); and the uniqueness of the
decomposition, `decomposition_unique`: any `ℝ`-algebra isomorphism of `M_I` with a product of
copies of `ℂ` agrees with `characterMap` up to reindexing and coordinatewise conjugation (via
`algHom_pi_complex_eq_coord`).
-/

import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LeanFormal.IUT.IUTIV.Estimates.ArchimedeanTensorMetric

open scoped ComplexConjugate TensorProduct
open PiTensorProduct Module

namespace LeanFormal.IUT.IUTIV.Estimates

section MultiTensor

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- The direct sum metric on `M = ⊕_{v ∈ V} ℂ_v`. -/
noncomputable def directSumComplexInner (m m' : V → ℂ) : ℝ := ∑ v, inner ℝ (m v) (m' v)

/-- `m ↦ ⟪m, ·⟫_M` as a linear map into the dual. -/
noncomputable def directSumComplexInnerDual : (V → ℂ) →ₗ[ℝ] Module.Dual ℝ (V → ℂ) where
  toFun m :=
    { toFun := fun m' => directSumComplexInner m m'
      map_add' := fun x y => by
        simp only [directSumComplexInner, Pi.add_apply, inner_add_right, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [directSumComplexInner, Pi.smul_apply, real_inner_smul_right, Finset.mul_sum,
          RingHom.id_apply, smul_eq_mul] }
  map_add' x y := by
    refine LinearMap.ext fun m' => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, directSumComplexInner,
      Pi.add_apply, inner_add_left, Finset.sum_add_distrib]
  map_smul' r x := by
    refine LinearMap.ext fun m' => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, directSumComplexInner,
      Pi.smul_apply, real_inner_smul_left, Finset.mul_sum, RingHom.id_apply, smul_eq_mul]

variable (I V) in
/-- The tensor product metric on `M_I = ⨂_{i ∈ I} M`, as a bilinear form. -/
noncomputable def tensorMetric :
    (⨂[ℝ] _i : I, (V → ℂ)) →ₗ[ℝ] Module.Dual ℝ (⨂[ℝ] _i : I, (V → ℂ)) :=
  dualDistrib ∘ₗ PiTensorProduct.map (fun _ => directSumComplexInnerDual)

omit [DecidableEq I] [DecidableEq V] in
theorem tensorMetric_tprod (a b : I → V → ℂ) :
    tensorMetric I V (tprod ℝ a) (tprod ℝ b) = ∏ i, directSumComplexInner (a i) (b i) := by
  simp [tensorMetric, map_tprod, dualDistrib_apply, directSumComplexInnerDual]

/-- `id` or complex conjugation, as `ℝ`-algebra endomorphisms of `ℂ`. -/
noncomputable def conjTwist (b : Bool) : ℂ →ₐ[ℝ] ℂ := if b then Complex.conjAe.toAlgHom
  else AlgHom.id ℝ ℂ

theorem conjTwist_apply (b : Bool) (z : ℂ) : conjTwist b z = if b then conj z else z := by
  cases b <;> rfl

variable (I V) in
/-- The index set of the decomposition: `|J| = |V|^{|I|} · 2^{|I|-1}`. -/
abbrev characterIndex (i₀ : I) : Type _ := (I → V) × ({i // i ≠ i₀} → Bool)

/-- The twist pattern on all of `I` (identity at `i₀`). -/
def twistPattern (i₀ : I) (σ : {i // i ≠ i₀} → Bool) (i : I) : Bool :=
  if h : i = i₀ then false else σ ⟨i, h⟩

/-- The coordinate `ℝ`-algebra map `M_I → ℂ` for the index `j`. -/
noncomputable def characterCoord (i₀ : I) (j : characterIndex I V i₀) :
    (⨂[ℝ] _i : I, (V → ℂ)) →ₐ[ℝ] ℂ :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra ℝ I ℂ).compLinearMap
      (fun i => (conjTwist (twistPattern i₀ j.2 i)).toLinearMap ∘ₗ LinearMap.proj (j.1 i)))
    (by simp [MultilinearMap.mkPiAlgebra_apply])
    (fun x y => by
      simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
        Pi.mul_apply, AlgHom.toLinearMap_apply, map_mul, Finset.prod_mul_distrib])

variable (I V) in
/-- **The decomposition map** `M_I → ∏_{j ∈ J} ℂ` (an `ℝ`-algebra map). -/
noncomputable def characterMap (i₀ : I) :
    (⨂[ℝ] _i : I, (V → ℂ)) →ₐ[ℝ] (characterIndex I V i₀ → ℂ) :=
  AlgHom.pi (fun j => characterCoord i₀ j)

omit [Fintype V] [DecidableEq V] in
theorem characterMap_tprod (i₀ : I) (a : I → V → ℂ) (j : characterIndex I V i₀) :
    characterMap I V i₀ (tprod ℝ a) j =
      ∏ i, conjTwist (twistPattern i₀ j.2 i) (a i (j.1 i)) := by
  simp [characterMap, characterCoord, MultilinearMap.mkPiAlgebra_apply]

/-- Split a product over `I` at `i₀`. -/
theorem prod_eq_mul_prod_subtype_ne' {M : Type*} [CommMonoid M] (i₀ : I) (f : I → M) :
    ∏ i, f i = f i₀ * ∏ k : {i // i ≠ i₀}, f k := by
  rw [Fintype.prod_eq_mul_prod_compl i₀,
    Finset.prod_subtype ({i₀}ᶜ) (p := fun x => x ≠ i₀) (fun x => by simp)]

theorem card_subtype_ne (i₀ : I) : Fintype.card {i // i ≠ i₀} = Fintype.card I - 1 := by
  simp [Fintype.card_subtype_compl]

/-- `∑_σ ∏_i σ_i(z_i) = z_{i₀} · ∏_{i ≠ i₀} (z_i + z̄_i)` (with `σ_{i₀} = id`). -/
theorem sum_twistPattern_prod (i₀ : I) (z : I → ℂ) :
    ∑ σ : {i // i ≠ i₀} → Bool, ∏ i, conjTwist (twistPattern i₀ σ i) (z i) =
      z i₀ * ∏ k : {i // i ≠ i₀}, (z k + conj (z k)) := by
  have hsplit : ∀ σ : {i // i ≠ i₀} → Bool, ∏ i, conjTwist (twistPattern i₀ σ i) (z i) =
      z i₀ * ∏ k : {i // i ≠ i₀}, conjTwist (σ k) (z k) := by
    intro σ
    rw [prod_eq_mul_prod_subtype_ne' i₀]
    congr 1
    · simp [twistPattern, conjTwist_apply]
    · refine Finset.prod_congr rfl fun k _ => ?_
      simp [twistPattern, k.2]
  have hpair : ∀ k : {i // i ≠ i₀}, z k + conj (z k) = ∑ b : Bool, conjTwist b (z k) := by
    intro k
    rw [Fintype.sum_bool, conjTwist_apply, conjTwist_apply]
    simp [add_comm]
  simp_rw [hsplit, ← Finset.mul_sum, hpair]
  rw [Fintype.prod_sum]

/-- `Re(z · ∏ (w_k + w̄_k)) = 2^{|κ|} · Re z · ∏ Re w_k`. -/
theorem re_mul_prod_add_conj {κ : Type*} [Fintype κ] (z : ℂ) (w : κ → ℂ) :
    (z * ∏ k, (w k + conj (w k))).re = 2 ^ Fintype.card κ * (z.re * ∏ k, (w k).re) := by
  simp_rw [Complex.add_conj]
  rw [← Complex.ofReal_prod, Complex.re_mul_ofReal, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  ring

omit [DecidableEq V] in
/-- **The metric identity on pure tensors.** -/
theorem characterMap_inner_tprod (i₀ : I) (a b : I → V → ℂ) :
    directSumComplexInner (characterMap I V i₀ (tprod ℝ a)) (characterMap I V i₀ (tprod ℝ b)) =
      2 ^ (Fintype.card I - 1) * tensorMetric I V (tprod ℝ a) (tprod ℝ b) := by
  rw [tensorMetric_tprod, ← card_subtype_ne i₀]
  simp only [directSumComplexInner, characterMap_tprod, Complex.inner]
  have hc : ∀ j : characterIndex I V i₀,
      (∏ i, conjTwist (twistPattern i₀ j.2 i) (b i (j.1 i))) *
          conj (∏ i, conjTwist (twistPattern i₀ j.2 i) (a i (j.1 i))) =
        ∏ i, conjTwist (twistPattern i₀ j.2 i) (b i (j.1 i) * conj (a i (j.1 i))) := by
    intro j
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [conjTwist_apply, conjTwist_apply, conjTwist_apply]
    split_ifs <;> simp [map_mul]
  simp_rw [hc]
  rw [Fintype.sum_prod_type]
  dsimp only
  have hx : ∀ x : I → V, ∑ y : {i // i ≠ i₀} → Bool,
      (∏ i, conjTwist (twistPattern i₀ y i) (b i (x i) * conj (a i (x i)))).re =
        2 ^ Fintype.card {i // i ≠ i₀} * ∏ i, (b i (x i) * conj (a i (x i))).re := by
    intro x
    rw [← Complex.re_sum, sum_twistPattern_prod i₀ (fun i => b i (x i) * conj (a i (x i))),
      re_mul_prod_add_conj]
    congr 1
    exact (prod_eq_mul_prod_subtype_ne' i₀ (fun i => (b i (x i) * conj (a i (x i))).re)).symm
  rw [Finset.sum_congr rfl (fun x _ => hx x), ← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun i w => (b i w * conj (a i w)).re)).symm

omit [DecidableEq V] in
/-- **IUT IV Prop 1.5 (iii), metric part.**  Under the decomposition map
`M_I → ∏_{j ∈ J} ℂ`, the direct sum metric is `2^{|I|-1}` times the tensor product metric. -/
theorem characterMap_inner (i₀ : I) (x y : ⨂[ℝ] _i : I, (V → ℂ)) :
    directSumComplexInner (characterMap I V i₀ x) (characterMap I V i₀ y) =
      2 ^ (Fintype.card I - 1) * tensorMetric I V x y := by
  let Φ := (characterMap I V i₀).toLinearMap
  let L₁ : (⨂[ℝ] _i : I, (V → ℂ)) →ₗ[ℝ] (⨂[ℝ] _i : I, (V → ℂ)) →ₗ[ℝ] ℝ :=
    ((directSumComplexInnerDual (V := characterIndex I V i₀)).compl₂ Φ) ∘ₗ Φ
  let L₂ : (⨂[ℝ] _i : I, (V → ℂ)) →ₗ[ℝ] (⨂[ℝ] _i : I, (V → ℂ)) →ₗ[ℝ] ℝ :=
    ((2 : ℝ) ^ (Fintype.card I - 1)) • tensorMetric I V
  have hL : L₁ = L₂ := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun a => ?_)
    refine PiTensorProduct.ext (MultilinearMap.ext fun b => ?_)
    simpa [L₁, L₂, Φ, directSumComplexInnerDual] using characterMap_inner_tprod i₀ a b
  have := congrArg (fun L => L x y) hL
  simpa [L₁, L₂, Φ, directSumComplexInnerDual] using this

theorem norm_conjTwist (b : Bool) (z : ℂ) : ‖conjTwist b z‖ = ‖z‖ := by
  rw [conjTwist_apply]
  split_ifs <;> simp

omit [Fintype V] [DecidableEq V] in
/-- **IUT IV Prop 1.5 (iv).**  If every component `m_i(v)` has length `λ`, then every
coordinate of `⊗ m_i` in the decomposition has length `λ^{|I|}`; in particular
`⊗ m_i ∈ λ^{|I|} · B_I` (product of unit balls). -/
theorem characterMap_tprod_norm (i₀ : I) (lam : ℝ) (m : I → V → ℂ)
    (hm : ∀ i v, ‖m i v‖ = lam) (j : characterIndex I V i₀) :
    ‖characterMap I V i₀ (tprod ℝ m) j‖ = lam ^ Fintype.card I := by
  rw [characterMap_tprod, norm_prod]
  simp only [norm_conjTwist, hm, Finset.prod_const, Finset.card_univ]

omit [Fintype V] [DecidableEq V] in
theorem characterMap_tprod_mem_scaled_unitBall (i₀ : I) (lam : ℝ) (m : I → V → ℂ)
    (hm : ∀ i v, ‖m i v‖ = lam) :
    ∀ j : characterIndex I V i₀, ‖characterMap I V i₀ (tprod ℝ m) j‖ ≤ lam ^ Fintype.card I :=
  fun j => (characterMap_tprod_norm i₀ lam m hm j).le

omit [DecidableEq V] in
theorem card_characterIndex (i₀ : I) :
    Fintype.card (characterIndex I V i₀) =
      Fintype.card V ^ Fintype.card I * 2 ^ (Fintype.card I - 1) := by
  simp [characterIndex, Fintype.card_prod]

variable (V) in
/-- The real basis `{δ_v, i δ_v}` of `M = V → ℂ`, indexed by `V × Fin 2`. -/
noncomputable def directSumComplexBasis : Basis (V × Fin 2) ℝ (V → ℂ) :=
  (Pi.basis (fun _ : V => Complex.basisOneI)).reindex (Equiv.sigmaEquivProd V (Fin 2))

theorem directSumComplexBasis_apply (v : V) (k : Fin 2) :
    directSumComplexBasis V (v, k) = Pi.single v (Complex.basisOneI k) := by
  simp [directSumComplexBasis, Basis.reindex_apply, Pi.basis_apply]

theorem inner_basisOneI (k k' : Fin 2) :
    inner ℝ (Complex.basisOneI k) (Complex.basisOneI k') = if k = k' then (1 : ℝ) else 0 := by
  fin_cases k <;> fin_cases k' <;> simp [Complex.coe_basisOneI, Complex.inner]

/-- The basis `{δ_v, i δ_v}` is orthonormal for the direct sum metric. -/
theorem directSumComplexInner_basis (p q : V × Fin 2) :
    directSumComplexInner (directSumComplexBasis V p) (directSumComplexBasis V q) =
      if p = q then 1 else 0 := by
  obtain ⟨v, k⟩ := p
  obtain ⟨v', k'⟩ := q
  rw [directSumComplexBasis_apply, directSumComplexBasis_apply, directSumComplexInner,
    Finset.sum_eq_single v]
  · by_cases hv : v = v'
    · subst hv
      fin_cases k <;> fin_cases k' <;> simp [Prod.ext_iff, Complex.coe_basisOneI, Complex.inner]
    · simp [hv]
  · intro w _ hw
    simp [Pi.single_apply, hw]
  · simp

variable (I V) in
/-- The product basis of `M_I`. -/
noncomputable def tensorBasis : Basis (I → V × Fin 2) ℝ (⨂[ℝ] _i : I, (V → ℂ)) :=
  Basis.piTensorProduct (fun _ => directSumComplexBasis V)

omit [DecidableEq I] in
theorem tensorMetric_basis (p q : I → V × Fin 2) :
    tensorMetric I V (tensorBasis I V p) (tensorBasis I V q) = if p = q then 1 else 0 := by
  rw [tensorBasis, Basis.piTensorProduct_apply, Basis.piTensorProduct_apply, tensorMetric_tprod]
  simp_rw [directSumComplexInner_basis]
  by_cases h : p = q
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

omit [DecidableEq V] in
/-- The tensor product metric is the sum of squares of coordinates in the product basis. -/
theorem tensorMetric_self (x : ⨂[ℝ] _i : I, (V → ℂ)) :
    tensorMetric I V x x = ∑ p, ((tensorBasis I V).repr x p) ^ 2 := by
  classical
  conv_lhs => rw [← (tensorBasis I V).sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    tensorMetric_basis, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

omit [DecidableEq I] [DecidableEq V] in
theorem tensorMetric_self_eq_zero {x : ⨂[ℝ] _i : I, (V → ℂ)} (h : tensorMetric I V x x = 0) :
    x = 0 := by
  classical
  rw [tensorMetric_self] at h
  have hz : ∀ p, (tensorBasis I V).repr x p = 0 := fun p => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg
      ((tensorBasis I V).repr x q))).mp h p (Finset.mem_univ p)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact (tensorBasis I V).repr.injective (by ext p; simp [hz p])

omit [Fintype V] [DecidableEq V] in
/-- The decomposition map is injective. -/
theorem characterMap_injective [Finite V] (i₀ : I) :
    Function.Injective (characterMap I V i₀) := by
  classical
  haveI := Fintype.ofFinite V
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := characterMap_inner i₀ x x
  rw [hx] at h
  simp only [directSumComplexInner, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero] at h
  have h2 : (0 : ℝ) < 2 ^ (Fintype.card I - 1) := by positivity
  exact tensorMetric_self_eq_zero (by
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' h2.ne'
    · exact h')

omit [Fintype V] [DecidableEq V] in
/-- **IUT IV Prop 1.5 (iii), decomposition.**  The decomposition map
`M_I → ∏_{j ∈ J} ℂ` is bijective, i.e. an `ℝ`-algebra isomorphism onto a direct sum of
`|V|^{|I|} · 2^{|I|-1}` copies of `ℂ`. -/
theorem characterMap_bijective [Finite V] (i₀ : I) :
    Function.Bijective (characterMap I V i₀) := by
  classical
  haveI := Fintype.ofFinite V
  refine ⟨characterMap_injective i₀, ?_⟩
  haveI : FiniteDimensional ℝ (⨂[ℝ] _i : I, (V → ℂ)) :=
    Module.Finite.of_basis (tensorBasis I V)
  have hn : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hdim : Module.finrank ℝ (⨂[ℝ] _i : I, (V → ℂ)) =
      Module.finrank ℝ (characterIndex I V i₀ → ℂ) := by
    rw [Module.finrank_eq_card_basis (tensorBasis I V), Module.finrank_pi_fintype,
      Finset.sum_const, Finset.card_univ, card_characterIndex, Complex.finrank_real_complex,
      Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_pow]
    obtain ⟨n, hn'⟩ : ∃ n, Fintype.card I = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn).symm⟩
    rw [hn', Nat.add_sub_cancel, pow_succ]
    ring
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (characterMap I V i₀).toLinearMap)).mp (characterMap_injective i₀)

/-! ## Prop 1.5 (iii), last sentence: primitive automorphisms of the summands -/

/-- `α` acts on every summand `ℂ_v` of `M = ⊕_v ℂ_v` by a primitive automorphism
`z ↦ u_v · τ_v(z)` with `u_v ∈ {±1, ±i}` and `τ_v ∈ {id, conj}`. -/
def IsPrimitiveSummandAut (α : (V → ℂ) →ₗ[ℝ] (V → ℂ)) (u : V → ℂ) (τ : V → Bool) : Prop :=
  (∀ v, u v = 1 ∨ u v = -1 ∨ u v = Complex.I ∨ u v = -Complex.I) ∧
    ∀ m v, α m v = u v * conjTwist (τ v) (m v)

theorem conjTwist_ofReal (b : Bool) (r : ℝ) : conjTwist b (r : ℂ) = r := by
  cases b <;> simp

theorem conjTwist_conjTwist (a b : Bool) (z : ℂ) :
    conjTwist a (conjTwist b z) = conjTwist (xor a b) z := by
  cases a <;> cases b <;> simp [conjTwist_apply]

variable (I V) in
/-- The coordinate permutation induced by the summand twists `τ` (an involution). -/
def primitivePerm (i₀ : I) (τ : I → V → Bool) :
    characterIndex I V i₀ ≃ characterIndex I V i₀ where
  toFun j := (j.1, fun k => xor (xor (j.2 k) (τ k (j.1 k))) (τ i₀ (j.1 i₀)))
  invFun j := (j.1, fun k => xor (xor (j.2 k) (τ k (j.1 k))) (τ i₀ (j.1 i₀)))
  left_inv j := by
    refine Prod.ext rfl (funext fun k => ?_)
    simp only
    cases j.2 k <;> cases τ k (j.1 k) <;> cases τ i₀ (j.1 i₀) <;> rfl
  right_inv j := by
    refine Prod.ext rfl (funext fun k => ?_)
    simp only
    cases j.2 k <;> cases τ k (j.1 k) <;> cases τ i₀ (j.1 i₀) <;> rfl

/-- The unit weight of the coordinate `j`. -/
noncomputable def primitiveWeight (i₀ : I) (u : I → V → ℂ) (j : characterIndex I V i₀) : ℂ :=
  ∏ i, conjTwist (twistPattern i₀ j.2 i) (u i (j.1 i))

omit [Fintype I] [Fintype V] [DecidableEq V] in
theorem twist_pattern_primitivePerm (i₀ : I) (τ : I → V → Bool) (j : characterIndex I V i₀)
    (i : I) :
    xor (τ i₀ (j.1 i₀)) (twistPattern i₀ (primitivePerm I V i₀ τ j).2 i) =
      xor (twistPattern i₀ j.2 i) (τ i (j.1 i)) := by
  by_cases h : i = i₀
  · subst h
    simp [twistPattern]
  · simp only [twistPattern, h, dif_neg, not_false_eq_true, primitivePerm, Equiv.coe_fn_mk]
    cases j.2 ⟨i, h⟩ <;> cases τ i (j.1 i) <;> cases τ i₀ (j.1 i₀) <;> rfl

omit [Fintype V] [DecidableEq V] in
/-- **Coordinate form of the induced automorphism.** -/
theorem characterMap_map_primitive (i₀ : I) (α : I → (V → ℂ) →ₗ[ℝ] (V → ℂ))
    (u : I → V → ℂ) (τ : I → V → Bool) (hα : ∀ i, IsPrimitiveSummandAut (α i) (u i) (τ i))
    (x : ⨂[ℝ] _i : I, (V → ℂ)) (j : characterIndex I V i₀) :
    characterMap I V i₀ (PiTensorProduct.map α x) j =
      primitiveWeight i₀ u j *
        conjTwist (τ i₀ (j.1 i₀)) (characterMap I V i₀ x (primitivePerm I V i₀ τ j)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, PiTensorProduct.map_tprod,
      characterMap_tprod, characterMap_tprod]
    simp only [Complex.real_smul, map_mul, conjTwist_ofReal]
    rw [mul_left_comm]
    congr 1
    rw [map_prod, primitiveWeight, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(hα i).2, map_mul, conjTwist_conjTwist, conjTwist_conjTwist,
      twist_pattern_primitivePerm]
    simp [primitivePerm]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add, mul_add]

omit [Fintype V] [DecidableEq V] in
theorem conj_mul_self_primitiveWeight (i₀ : I) (u : I → V → ℂ)
    (hu : ∀ i v, u i v = 1 ∨ u i v = -1 ∨ u i v = Complex.I ∨ u i v = -Complex.I)
    (j : characterIndex I V i₀) :
    conj (primitiveWeight i₀ u j) * primitiveWeight i₀ u j = 1 := by
  rw [primitiveWeight, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [conjTwist_apply]
  rcases hu i (j.1 i) with h | h | h | h <;> rw [h] <;> split_ifs <;> simp

theorem inner_unitMul_conjTwist (w : ℂ) (hw : conj w * w = 1) (c : Bool) (z z' : ℂ) :
    inner ℝ (w * conjTwist c z) (w * conjTwist c z') = inner ℝ z z' := by
  have hw' : w.re * w.re + w.im * w.im = 1 := by
    have := congrArg Complex.re hw
    simpa [Complex.mul_re, Complex.conj_re, Complex.conj_im] using this
  cases c <;>
  · simp only [conjTwist_apply, Complex.inner, Bool.false_eq_true, if_false, if_true,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, map_mul]
    linear_combination (z.re * z'.re + z.im * z'.im) * hw'

omit [DecidableEq V] in
/-- **IUT IV Prop 1.5 (iii), last sentence.**  Automorphisms of `M_I` induced by primitive
automorphisms of the summands `ℂ_v` of the factors preserve the direct sum metric (and, via
`characterMap_coord_norm_map_primitive`, the integral structure `B_I`). -/
theorem directSumInner_map_primitive (i₀ : I) (α : I → (V → ℂ) →ₗ[ℝ] (V → ℂ))
    (u : I → V → ℂ) (τ : I → V → Bool) (hα : ∀ i, IsPrimitiveSummandAut (α i) (u i) (τ i))
    (x y : ⨂[ℝ] _i : I, (V → ℂ)) :
    directSumComplexInner (characterMap I V i₀ (PiTensorProduct.map α x))
        (characterMap I V i₀ (PiTensorProduct.map α y)) =
      directSumComplexInner (characterMap I V i₀ x) (characterMap I V i₀ y) := by
  have hu : ∀ i v, u i v = 1 ∨ u i v = -1 ∨ u i v = Complex.I ∨ u i v = -Complex.I :=
    fun i => (hα i).1
  simp only [directSumComplexInner, characterMap_map_primitive i₀ α u τ hα,
    inner_unitMul_conjTwist _ (conj_mul_self_primitiveWeight i₀ u hu _)]
  exact Equiv.sum_comp (primitivePerm I V i₀ τ)
    (fun j => inner ℝ (characterMap I V i₀ x j) (characterMap I V i₀ y j))

omit [DecidableEq I] [DecidableEq V] in
/-- The tensor product metric is preserved too. -/
theorem tensorMetric_map_primitive (i₀ : I) (α : I → (V → ℂ) →ₗ[ℝ] (V → ℂ))
    (u : I → V → ℂ) (τ : I → V → Bool) (hα : ∀ i, IsPrimitiveSummandAut (α i) (u i) (τ i))
    (x y : ⨂[ℝ] _i : I, (V → ℂ)) :
    tensorMetric I V (PiTensorProduct.map α x) (PiTensorProduct.map α y) =
      tensorMetric I V x y := by
  classical
  have h := directSumInner_map_primitive i₀ α u τ hα x y
  rw [characterMap_inner, characterMap_inner] at h
  have h2 : (0 : ℝ) < 2 ^ (Fintype.card I - 1) := by positivity
  exact mul_left_cancel₀ h2.ne' h

omit [Fintype V] [DecidableEq V] in
/-- The decomposition coordinates are permuted (up to units and conjugation), so the
integral structure `B_I` (product of unit balls) is preserved. -/
theorem characterMap_coord_norm_map_primitive (i₀ : I) (α : I → (V → ℂ) →ₗ[ℝ] (V → ℂ))
    (u : I → V → ℂ) (τ : I → V → Bool) (hα : ∀ i, IsPrimitiveSummandAut (α i) (u i) (τ i))
    (x : ⨂[ℝ] _i : I, (V → ℂ)) (j : characterIndex I V i₀) :
    ‖characterMap I V i₀ (PiTensorProduct.map α x) j‖ =
      ‖characterMap I V i₀ x (primitivePerm I V i₀ τ j)‖ := by
  have hu : ∀ i v, u i v = 1 ∨ u i v = -1 ∨ u i v = Complex.I ∨ u i v = -Complex.I :=
    fun i => (hα i).1
  have hw := conj_mul_self_primitiveWeight i₀ u hu j
  have hnorm : ‖primitiveWeight i₀ u j‖ = 1 := by
    have hn : Complex.normSq (primitiveWeight i₀ u j) = 1 := by
      have := Complex.normSq_eq_conj_mul_self (z := primitiveWeight i₀ u j)
      rw [hw] at this
      exact_mod_cast this
    have : ‖primitiveWeight i₀ u j‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, hn]
    nlinarith [norm_nonneg (primitiveWeight i₀ u j)]
  rw [characterMap_map_primitive i₀ α u τ hα, norm_mul, hnorm, one_mul, norm_conjTwist]

/-! ## Prop 1.5 (iii): uniqueness of the decomposition -/

/-- Every `ℝ`-algebra map `∏_{j ∈ J} ℂ → ℂ` is a coordinate projection followed by the
identity or complex conjugation. -/
theorem algHom_pi_complex_eq_coord {J : Type*} [Finite J]
    (f : (J → ℂ) →ₐ[ℝ] ℂ) : ∃ (j : J) (c : Bool), ∀ x, f x = conjTwist c (x j) := by
  classical
  haveI := Fintype.ofFinite J
  have hidem : ∀ j, f (Pi.single j 1) = 0 ∨ f (Pi.single j 1) = 1 := fun j =>
    complex_idempotent_eq_zero_or_one (by
      rw [← map_mul, ← Pi.single_mul, mul_one])
  have hsum : ∑ j, f (Pi.single j 1) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : ℂ))]
    exact map_one f
  obtain ⟨j, hj⟩ : ∃ j, f (Pi.single j 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ j, f (Pi.single j 1) = 0 :=
      Finset.sum_eq_zero fun j _ => (hidem j).resolve_right (h j)
    rw [hsum] at this
    exact one_ne_zero this
  let g : ℂ →ₐ[ℝ] ℂ :=
    { toFun := fun z => f (Pi.single j z)
      map_one' := hj
      map_mul' := fun z w => by rw [Pi.single_mul, map_mul]
      map_zero' := by simp
      map_add' := fun z w => by rw [Pi.single_add, map_add]
      commutes' := fun r => by
        have : (Pi.single j (algebraMap ℝ ℂ r) : J → ℂ) = r • Pi.single j 1 := by
          ext k; by_cases hk : k = j <;> simp [hk, Algebra.smul_def]
        rw [this, map_smul, hj, Algebra.smul_def, mul_one] }
  have hcoord : ∀ x : J → ℂ, f x = g (x j) := fun x => by
    have hx : x * Pi.single j 1 = Pi.single j (x j) := by
      ext k; by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    calc f x = f x * f (Pi.single j 1) := by rw [hj, mul_one]
      _ = f (Pi.single j (x j)) := by rw [← map_mul, hx]
      _ = g (x j) := rfl
  rcases Complex.real_algHom_eq_id_or_conj g with hg | hg
  · exact ⟨j, false, fun x => by rw [hcoord, hg]; rfl⟩
  · exact ⟨j, true, fun x => by rw [hcoord, hg]; rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- **IUT IV Prop 1.5 (iii), uniqueness of the decomposition.**  Any decomposition of `M_I`
as an `ℝ`-algebra into a product of copies of `ℂ` agrees with `characterMap` up to a
bijection of the index sets and complex conjugation on individual coordinates. -/
theorem decomposition_unique [Finite V] (i₀ : I) {J' : Type*} [Finite J']
    (ψ : (⨂[ℝ] _i : I, (V → ℂ)) ≃ₐ[ℝ] (J' → ℂ)) :
    ∃ (π : J' ≃ characterIndex I V i₀) (c : J' → Bool),
      ∀ x j', ψ x j' = conjTwist (c j') (characterMap I V i₀ x (π j')) := by
  classical
  haveI := Fintype.ofFinite V
  haveI := Fintype.ofFinite J'
  let Φe := AlgEquiv.ofBijective (characterMap I V i₀) (characterMap_bijective i₀)
  let σ : (characterIndex I V i₀ → ℂ) ≃ₐ[ℝ] (J' → ℂ) := Φe.symm.trans ψ
  have hcoord : ∀ j' : J', ∃ (j : characterIndex I V i₀) (c : Bool),
      ∀ y, σ y j' = conjTwist c (y j) := fun j' =>
    algHom_pi_complex_eq_coord ((Pi.evalAlgHom ℝ (fun _ => ℂ) j').comp σ.toAlgHom)
  choose πf c hc using hcoord
  have hinj : Function.Injective πf := by
    intro j₁ j₂ h
    by_contra hne
    obtain ⟨y, hy⟩ := σ.surjective (Pi.single j₁ 1)
    have h1 := hc j₁ y
    have h2 := hc j₂ y
    rw [hy, Pi.single_eq_same] at h1
    rw [hy, Pi.single_eq_of_ne (Ne.symm hne), ← h] at h2
    rw [conjTwist_apply] at h1 h2
    have ha : y (πf j₁) = 0 := by
      split_ifs at h2
      · simpa using h2.symm
      · exact h2.symm
    rw [ha] at h1
    split_ifs at h1 <;> simp at h1
  have hcard : Fintype.card J' = Fintype.card (characterIndex I V i₀) := by
    have := σ.toLinearEquiv.finrank_eq
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at this
    simp only [Finset.sum_const, Finset.card_univ, Complex.finrank_real_complex,
      smul_eq_mul] at this
    omega
  let π : J' ≃ characterIndex I V i₀ :=
    Equiv.ofBijective πf ((Fintype.bijective_iff_injective_and_card πf).mpr ⟨hinj, hcard⟩)
  refine ⟨π, c, fun x j' => ?_⟩
  have hx : ψ x = σ (characterMap I V i₀ x) := by
    simp [σ, Φe]
  rw [hx, hc]
  rfl

end MultiTensor

end LeanFormal.IUT.IUTIV.Estimates
