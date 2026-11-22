import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorArrowRealization
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTensorIndex
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorEquivalence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Composition compatibility of the coordinate-arrow ↔ equivariant-map dictionary

Layer 3e (closing the review gap: the dictionary of
`Example36TorsorArrowRealization` was not yet proved compatible with actual
composition).

Contents:

* composition and identity of `F^x`-torsor homomorphisms, the coordinate
  lemma `TorsorHom.coordinate_map`, and the induced torsor homomorphisms of
  torsor isomorphisms (in both directions);
* the m-fold tensor power `α^⊗m` of a torsor homomorphism `α`, with its
  computation rule on tensor points;
* the canonical flattening isomorphism
  `(T^⊗n)^⊗m ≅ T^⊗(n*m)` of contracted products, with its computation rule on
  tensor points and its coordinate compatibility;
* the actual-map composition law
  `α_{ψ∘φ} = α_ψ ∘ (α_φ)^⊗m ∘ flatten⁻¹`, together with the arrow degree
  `m*n` and multiplier `g * f^m`, and the identity correspondence
  `α_{id P} = (T^⊗1 ≅ T)`;
* the base-point caveat: a base-point change of a presentation gives a
  degree-1 `TorsorArrow` isomorphism (with multiplier `h⁻¹`), while
  `PresentationIso` fixes the base point and every local point and is a
  strictly stronger, non-equivalent notion; it is not the class of all
  invertible arrows.

Boundary: no source Hodge theater, theta-pilot or q-pilot claim.  Everything
here is the elementary contracted-product/torsor bookkeeping of III Example
3.6; the tensor power is the one with the residual action through a chosen
coordinate (any coordinate works, by `Example36TorsorTensorIndex`).
-/



noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open GTorsorTensor TensorIndex
open scoped BigOperators

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. Composition and identity of torsor homomorphisms -/

/-- Composition of torsor homomorphisms: apply the first, then the second. -/
def TorsorHom.comp {T₁ T₂ T₃ : GTorsor Fˣ} (α : TorsorHom T₁ T₂)
    (β : TorsorHom T₂ T₃) : TorsorHom T₁ T₃ where
  toFun := β.toFun ∘ α.toFun
  map_smul := fun g x => by
    change β.toFun (α.toFun (g • x)) = g • β.toFun (α.toFun x)
    rw [α.map_smul, β.map_smul]

@[simp]
theorem TorsorHom.comp_apply {T₁ T₂ T₃ : GTorsor Fˣ} (α : TorsorHom T₁ T₂)
    (β : TorsorHom T₂ T₃) (x : T₁.carrier) :
    (α.comp β).toFun x = β.toFun (α.toFun x) := rfl

/-- The identity torsor homomorphism. -/
def TorsorHom.id (T : GTorsor Fˣ) : TorsorHom T T where
  toFun := fun x => x
  map_smul := fun _ _ => rfl

@[simp]
theorem TorsorHom.id_apply (T : GTorsor Fˣ) (x : T.carrier) :
    (TorsorHom.id T).toFun x = x := rfl

@[simp]
theorem TorsorHom.id_comp {T₁ T₂ : GTorsor Fˣ} (α : TorsorHom T₁ T₂) :
    (TorsorHom.id T₁).comp α = α := by
  apply TorsorHom.ext
  funext x
  rfl

@[simp]
theorem TorsorHom.comp_id {T₁ T₂ : GTorsor Fˣ} (α : TorsorHom T₁ T₂) :
    α.comp (TorsorHom.id T₂) = α := by
  apply TorsorHom.ext
  funext x
  rfl

/-- Every torsor homomorphism preserves torsor coordinates relative to the
images of a base point. -/
theorem TorsorHom.coordinate_map {T₁ T₂ : GTorsor Fˣ} (α : TorsorHom T₁ T₂)
    (t x : T₁.carrier) :
    T₂.coordinate (α.toFun t) (α.toFun x) = T₁.coordinate t x := by
  have hx : x = T₁.coordinate t x • t := (GTorsor.coordinate_spec T₁ t x).symm
  conv_lhs => rw [hx]
  rw [α.map_smul, GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]

namespace TensorIndex

/-- A torsor isomorphism as a torsor homomorphism. -/
def GTorsorEquiv.toTorsorHom {T₁ T₂ : GTorsor Fˣ} (e : GTorsorEquiv T₁ T₂) :
    TorsorHom T₁ T₂ where
  toFun := e.toFun
  map_smul := e.map_smul

@[simp]
theorem GTorsorEquiv.toTorsorHom_apply {T₁ T₂ : GTorsor Fˣ}
    (e : GTorsorEquiv T₁ T₂) (x : T₁.carrier) :
    e.toTorsorHom.toFun x = e.toFun x := rfl

/-- The inverse map of a torsor isomorphism is again equivariant. -/
theorem GTorsorEquiv.invFun_smul {T₁ T₂ : GTorsor Fˣ} (e : GTorsorEquiv T₁ T₂)
    (g : Fˣ) (y : T₂.carrier) :
    e.invFun (g • y) = g • e.invFun y := by
  have h : e.toFun (e.invFun (g • y)) = e.toFun (g • e.invFun y) := by
    rw [e.right_inv, e.map_smul, e.right_inv]
  calc e.invFun (g • y)
      = e.invFun (e.toFun (e.invFun (g • y))) :=
        (e.left_inv (e.invFun (g • y))).symm
    _ = e.invFun (e.toFun (g • e.invFun y)) := by rw [h]
    _ = g • e.invFun y := e.left_inv (g • e.invFun y)

/-- The inverse of a torsor isomorphism, as a torsor homomorphism. -/
def GTorsorEquiv.symmTorsorHom {T₁ T₂ : GTorsor Fˣ} (e : GTorsorEquiv T₁ T₂) :
    TorsorHom T₂ T₁ where
  toFun := e.invFun
  map_smul := e.invFun_smul

@[simp]
theorem GTorsorEquiv.symmTorsorHom_apply {T₁ T₂ : GTorsor Fˣ}
    (e : GTorsorEquiv T₁ T₂) (y : T₂.carrier) :
    e.symmTorsorHom.toFun y = e.invFun y := rfl

end TensorIndex

/-! ## 2. The m-fold tensor power of a torsor homomorphism -/

/-- The underlying function of the m-fold tensor power map of a torsor
homomorphism, on representatives. -/
def TorsorHom.tensorPowerAtFun {T₁ T₂ : GTorsor Fˣ} (α : TorsorHom T₁ T₂) (m : ℕ) :
    (Fin m → T₁.carrier) → tensorCarrier T₂ m :=
  fun x => Quotient.mk (tensorSetoid T₂ m) (fun j => α.toFun (x j))

@[simp]
theorem TorsorHom.tensorPowerAtFun_apply {T₁ T₂ : GTorsor Fˣ}
    (α : TorsorHom T₁ T₂) (m : ℕ) (x : Fin m → T₁.carrier) :
    α.tensorPowerAtFun m x =
      Quotient.mk (tensorSetoid T₂ m) (fun j => α.toFun (x j)) := rfl

/-- The coordinatewise application of a torsor homomorphism preserves the
multiplier relation, hence descends to contracted products. -/
theorem TorsorHom.tensorPowerAtFun_wellDefined {T₁ T₂ : GTorsor Fˣ}
    (α : TorsorHom T₁ T₂) (m : ℕ) :
    ∀ a b : Fin m → T₁.carrier, tensorRel T₁ m a b →
      α.tensorPowerAtFun m a = α.tensorPowerAtFun m b := by
  intro a b hab
  obtain ⟨mm, hm, hprod⟩ := hab
  rw [TorsorHom.tensorPowerAtFun_apply, TorsorHom.tensorPowerAtFun_apply]
  apply Quotient.sound
  refine ⟨mm, ?_, hprod⟩
  intro j
  change α.toFun (b j) = mm j • α.toFun (a j)
  rw [hm j, α.map_smul]

/-- The m-fold tensor power of a torsor homomorphism `α : T₁ → T₂`: the
induced equivariant map `T₁^⊗m → T₂^⊗m` on contracted products, defined on
representatives by applying `α` coordinatewise.  Well defined because `α` is
equivariant, and equivariant because the residual action is a
first-coordinate update. -/
def TorsorHom.tensorPowerAt {T₁ T₂ : GTorsor Fˣ} (α : TorsorHom T₁ T₂)
    (m : ℕ) (j0 : Fin m) :
    TorsorHom (tensorPowerAt T₁ m j0) (tensorPowerAt T₂ m j0) where
  toFun := Quotient.lift (α.tensorPowerAtFun m) (α.tensorPowerAtFun_wellDefined m)
  map_smul := by
    intro g q
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.lift (α.tensorPowerAtFun m) (α.tensorPowerAtFun_wellDefined m)
        (tensorSMul T₁ m j0 g (Quotient.mk (tensorSetoid T₁ m) x)) =
      tensorSMul T₂ m j0 g
        (Quotient.lift (α.tensorPowerAtFun m) (α.tensorPowerAtFun_wellDefined m)
          (Quotient.mk (tensorSetoid T₁ m) x))
    rw [tensorSMul_mk, show Quotient.lift (α.tensorPowerAtFun m)
        (α.tensorPowerAtFun_wellDefined m)
        (Quotient.mk (tensorSetoid T₁ m) (Function.update x j0 (g • x j0))) =
        α.tensorPowerAtFun m (Function.update x j0 (g • x j0)) from rfl,
      show Quotient.lift (α.tensorPowerAtFun m) (α.tensorPowerAtFun_wellDefined m)
        (Quotient.mk (tensorSetoid T₁ m) x) = α.tensorPowerAtFun m x from rfl]
    simp only [TorsorHom.tensorPowerAtFun_apply, tensorSMul_mk]
    apply Quotient.sound
    refine ⟨fun _ => 1, ?_, by simp⟩
    intro j
    rw [one_smul]
    by_cases hj : j = j0
    · subst hj
      simp only [Function.update_self, α.map_smul]
    · simp only [Function.update_of_ne hj]

@[simp]
theorem TorsorHom.tensorPowerAt_apply_mk {T₁ T₂ : GTorsor Fˣ}
    (α : TorsorHom T₁ T₂) (m : ℕ) (j0 : Fin m)
    (x : Fin m → T₁.carrier) :
    ((α.tensorPowerAt m j0).toFun (Quotient.mk (tensorSetoid T₁ m) x) :
        tensorCarrier T₂ m) =
      Quotient.mk (tensorSetoid T₂ m) (fun j => α.toFun (x j)) := by
  rw [TorsorHom.tensorPowerAt]
  rfl

@[simp]
theorem TorsorHom.tensorPowerAt_tensorPoint {T₁ T₂ : GTorsor Fˣ}
    (α : TorsorHom T₁ T₂) (m : ℕ) (j0 : Fin m) (x : T₁.carrier) :
    ((α.tensorPowerAt m j0).toFun (tensorPoint T₁ m x) : tensorCarrier T₂ m) =
      tensorPoint T₂ m (α.toFun x) := by
  rw [tensorPoint, TorsorHom.tensorPowerAt_apply_mk, tensorPoint]

/-! ## 3. The canonical flattening `(T^⊗n)^⊗m ≅ T^⊗(n*m)` -/

/-- The nested tensor base point: the m-fold tensor of the n-fold tensor of a
point `t`.  It is the source base point of the flattening map. -/
def nestedTensorBase (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n) (m : ℕ) (j0 : Fin m)
    (t : T.carrier) : (tensorPowerAt (tensorPowerAt T n i0) m j0).carrier :=
  tensorPoint (tensorPowerAt T n i0) m (tensorPoint T n t)

/-- The canonical flattening homomorphism
`(T^⊗n)^⊗m → T^⊗(n*m)`: the unique equivariant map which sends the nested
tensor base point to the tensor base point. -/
def tensorFlattenHom (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n) (m : ℕ) (j0 : Fin m)
    (k0 : Fin (m * n)) :
    TorsorHom (tensorPowerAt (tensorPowerAt T n i0) m j0)
      (tensorPowerAt T (m * n) k0) :=
  TorsorHom.ofPoint (nestedTensorBase T n i0 m j0 (Classical.choice T.nonempty))
    (tensorPoint T (m * n) (Classical.choice T.nonempty))

/-- **Computation rule of the flattening on tensor points:** the flattening
sends the nested tensor point of `x` to the `(n*m)`-fold tensor point of `x`. -/
theorem tensorFlattenHom_tensorPoint (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)
    (m : ℕ) (j0 : Fin m) (k0 : Fin (m * n)) (x : T.carrier) :
    ((tensorFlattenHom T n i0 m j0 k0).toFun
        (nestedTensorBase T n i0 m j0 x) : tensorCarrier T (m * n)) =
      tensorPoint T (m * n) x := by
  set t : T.carrier := Classical.choice T.nonempty
  letI : MulAction Fˣ (tensorCarrier T (m * n)) := tensorMulAction T (m * n) k0
  have hcoord : (tensorPowerAt (tensorPowerAt T n i0) m j0).coordinate
      (nestedTensorBase T n i0 m j0 t) (nestedTensorBase T n i0 m j0 x) =
      (T.coordinate t x) ^ (m * n) := by
    rw [nestedTensorBase, nestedTensorBase,
      tensorPowerAt_coordinate_tensorPoint (tensorPowerAt T n i0) m j0,
      tensorPowerAt_coordinate_tensorPoint T n i0, ← pow_mul, Nat.mul_comm]
  change tensorSMul T (m * n) k0
      ((tensorPowerAt (tensorPowerAt T n i0) m j0).coordinate
        (nestedTensorBase T n i0 m j0 t) (nestedTensorBase T n i0 m j0 x))
      (tensorPoint T (m * n) t) = tensorPoint T (m * n) x
  rw [hcoord]
  have hspec := GTorsor.coordinate_spec (tensorPowerAt T (m * n) k0)
    (tensorPoint T (m * n) t) (tensorPoint T (m * n) x)
  rw [tensorPowerAt_coordinate_tensorPoint T (m * n) k0 t x] at hspec
  exact hspec

/-- **Coordinate compatibility of the flattening:** the coordinate of the
flattening of `q` relative to the image of the nested base point is the
coordinate of `q` relative to that base point. -/
theorem tensorFlattenHom_coordinate (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)
    (m : ℕ) (j0 : Fin m) (k0 : Fin (m * n))
    (q : (tensorPowerAt (tensorPowerAt T n i0) m j0).carrier) :
    (tensorPowerAt T (m * n) k0).coordinate
        (tensorPoint T (m * n) (Classical.choice T.nonempty))
        ((tensorFlattenHom T n i0 m j0 k0).toFun q) =
      (tensorPowerAt (tensorPowerAt T n i0) m j0).coordinate
        (nestedTensorBase T n i0 m j0 (Classical.choice T.nonempty)) q := by
  have hbase : (tensorFlattenHom T n i0 m j0 k0).toFun
      (nestedTensorBase T n i0 m j0 (Classical.choice T.nonempty)) =
      tensorPoint T (m * n) (Classical.choice T.nonempty) :=
    tensorFlattenHom_tensorPoint T n i0 m j0 k0 _
  rw [← hbase]
  exact TorsorHom.coordinate_map (tensorFlattenHom T n i0 m j0 k0) _ q

/-- The flattening homomorphism is bijective (every equivariant map of torsors
is), hence an isomorphism of torsors. -/
theorem tensorFlattenHom_bijective (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)
    (m : ℕ) (j0 : Fin m) (k0 : Fin (m * n)) :
    Function.Bijective (tensorFlattenHom T n i0 m j0 k0).toFun := by
  exact GTorsor.equivariantMapOfPoint_bijective
    (tensorPowerAt (tensorPowerAt T n i0) m j0) (tensorPowerAt T (m * n) k0)
    (nestedTensorBase T n i0 m j0 (Classical.choice T.nonempty))
    (tensorPoint T (m * n) (Classical.choice T.nonempty))

/-- The canonical flattening isomorphism of contracted products
`(T^⊗n)^⊗m ≅ T^⊗(n*m)`. -/
noncomputable def tensorFlattenEquiv (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)
    (m : ℕ) (j0 : Fin m) (k0 : Fin (m * n)) :
    GTorsorEquiv (tensorPowerAt (tensorPowerAt T n i0) m j0)
      (tensorPowerAt T (m * n) k0) := by
  let e : (tensorPowerAt (tensorPowerAt T n i0) m j0).carrier ≃
      (tensorPowerAt T (m * n) k0).carrier :=
    Equiv.ofBijective (tensorFlattenHom T n i0 m j0 k0).toFun
      (tensorFlattenHom_bijective T n i0 m j0 k0)
  exact
    { toFun := e.toFun
      invFun := e.invFun
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_smul := (tensorFlattenHom T n i0 m j0 k0).map_smul }

/-- The flattening isomorphism applied to a tensor point is the tensor point. -/
@[simp]
theorem tensorFlattenEquiv_tensorPoint (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)
    (m : ℕ) (j0 : Fin m) (k0 : Fin (m * n)) (x : T.carrier) :
    ((tensorFlattenEquiv T n i0 m j0 k0).toFun
        (nestedTensorBase T n i0 m j0 x) : tensorCarrier T (m * n)) =
      tensorPoint T (m * n) x :=
  tensorFlattenHom_tensorPoint T n i0 m j0 k0 x

/-- The inverse of the flattening on tensor points is the nested tensor base
point. -/
@[simp]
theorem tensorFlattenEquiv_symm_tensorPoint (T : GTorsor Fˣ) (n : ℕ) (i0 : Fin n)
    (m : ℕ) (j0 : Fin m) (k0 : Fin (m * n)) (x : T.carrier) :
    ((tensorFlattenEquiv T n i0 m j0 k0).invFun (tensorPoint T (m * n) x) :
        tensorCarrier (tensorPowerAt T n i0) m) =
      nestedTensorBase T n i0 m j0 x := by
  have hbase := tensorFlattenEquiv_tensorPoint T n i0 m j0 k0 x
  have hinv := (tensorFlattenEquiv T n i0 m j0 k0).left_inv
    (nestedTensorBase T n i0 m j0 x)
  rw [hbase] at hinv
  exact hinv

/-! ## 4. Composition of arrows and the actual-map composition law -/

/-- The general computation rule for the equivariant map determined by a base
point and an image point. -/
@[simp]
theorem TorsorHom.ofPoint_toFun {T₁ T₂ : GTorsor Fˣ} (x₁ : T₁.carrier)
    (y₂ : T₂.carrier) (q : T₁.carrier) :
    (TorsorHom.ofPoint x₁ y₂).toFun q = T₁.coordinate x₁ q • y₂ := rfl

/-- The actual equivariant map of an arrow, evaluated at a tensor point. -/
theorem TorsorArrow.toTorsorHom_tensorPoint {D : GlobalPlaceData F}
    {P₁ P₂ : TorsorPresentation D} (φ : TorsorArrow P₁ P₂) (y : P₁.T.carrier) :
    φ.toTorsorHom.toFun
        (tensorPoint P₁.T φ.degree y) =
      ((P₁.T.coordinate P₁.base y) ^ φ.degree * φ.multiplier) • P₂.base := by
  rw [TorsorArrow.toTorsorHom, TorsorHom.ofPoint_toFun,
    tensorPowerAt_coordinate_tensorPoint, ← mul_smul]

/-- The actual map of the composite arrow, written in the contracted-product
form `α_ψ ∘ (α_φ)^⊗m ∘ flatten⁻¹`. -/
def TorsorArrow.compActualMap {D : GlobalPlaceData F} {P₁ P₂ P₃ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    TorsorHom (tensorPowerAt P₁.T (ψ.degree * φ.degree)
      (tensorPowerAtOfIndex (TorsorArrow.comp φ ψ).positive_degree)) P₃.T :=
  (tensorFlattenEquiv (T := P₁.T) φ.degree (tensorPowerAtOfIndex φ.positive_degree)
      ψ.degree (tensorPowerAtOfIndex ψ.positive_degree)
      (tensorPowerAtOfIndex (TorsorArrow.comp φ ψ).positive_degree)).symmTorsorHom.comp
    ((φ.toTorsorHom.tensorPowerAt ψ.degree
        (tensorPowerAtOfIndex ψ.positive_degree)).comp ψ.toTorsorHom)

/-- The degree of a composite arrow is `m*n`. -/
@[simp]
theorem TorsorArrow.comp_degree {D : GlobalPlaceData F} {P₁ P₂ P₃ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    (TorsorArrow.comp φ ψ).degree = ψ.degree * φ.degree := rfl

/-- The multiplier of a composite arrow is `g * f^m`. -/
@[simp]
theorem TorsorArrow.comp_multiplier {D : GlobalPlaceData F}
    {P₁ P₂ P₃ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    (TorsorArrow.comp φ ψ).multiplier = ψ.multiplier * φ.multiplier ^ ψ.degree := rfl

/-- **Actual-map composition law.**  For `φ : P₁ → P₂` and `ψ : P₂ → P₃`, the
equivariant map of the composite arrow is
`α_ψ ∘ (α_φ)^⊗m ∘ flatten⁻¹`, where `m = ψ.degree` and the composite arrow has
degree `m*n` and multiplier `g * f^m`. -/
theorem TorsorArrow.toTorsorHom_comp {D : GlobalPlaceData F}
    {P₁ P₂ P₃ : TorsorPresentation D} (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    (TorsorArrow.comp φ ψ).toTorsorHom =
      TorsorArrow.compActualMap φ ψ := by
  apply TorsorHom.ext_of_base
    (x₁ := tensorPoint P₁.T (ψ.degree * φ.degree) P₁.base)
  have hL : (TorsorArrow.comp φ ψ).toTorsorHom.toFun
      (tensorPoint P₁.T (ψ.degree * φ.degree) P₁.base) =
      (TorsorArrow.comp φ ψ).multiplier • P₃.base :=
    TorsorArrow.toTorsorHom_apply_base (φ := TorsorArrow.comp φ ψ)
  have hflat : (tensorFlattenEquiv (T := P₁.T) φ.degree
      (tensorPowerAtOfIndex φ.positive_degree) ψ.degree
      (tensorPowerAtOfIndex ψ.positive_degree)
      (tensorPowerAtOfIndex (TorsorArrow.comp φ ψ).positive_degree)).invFun
      (tensorPoint P₁.T (ψ.degree * φ.degree) P₁.base) =
      nestedTensorBase P₁.T φ.degree (tensorPowerAtOfIndex φ.positive_degree)
        ψ.degree (tensorPowerAtOfIndex ψ.positive_degree) P₁.base :=
    tensorFlattenEquiv_symm_tensorPoint P₁.T φ.degree _ ψ.degree _ _ P₁.base
  have hten : (φ.toTorsorHom.tensorPowerAt ψ.degree
      (tensorPowerAtOfIndex ψ.positive_degree)).toFun
      (nestedTensorBase P₁.T φ.degree (tensorPowerAtOfIndex φ.positive_degree)
        ψ.degree (tensorPowerAtOfIndex ψ.positive_degree) P₁.base) =
      tensorPoint P₂.T ψ.degree (φ.multiplier • P₂.base) := by
    rw [show nestedTensorBase P₁.T φ.degree (tensorPowerAtOfIndex φ.positive_degree)
        ψ.degree (tensorPowerAtOfIndex ψ.positive_degree) P₁.base =
        tensorPoint (tensorPowerAt P₁.T φ.degree
          (tensorPowerAtOfIndex φ.positive_degree)) ψ.degree
          (tensorPoint P₁.T φ.degree P₁.base) from rfl]
    rw [TorsorHom.tensorPowerAt_tensorPoint, TorsorArrow.toTorsorHom_apply_base]
  have hpsi := TorsorArrow.toTorsorHom_tensorPoint (φ := ψ)
    (y := φ.multiplier • P₂.base)
  have hcoord : P₂.T.coordinate P₂.base (φ.multiplier • P₂.base) =
      φ.multiplier := by
    rw [GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]
  have hR : (TorsorArrow.compActualMap φ ψ).toFun
      (tensorPoint P₁.T (ψ.degree * φ.degree) P₁.base) =
      (φ.multiplier ^ ψ.degree * ψ.multiplier) • P₃.base := by
    rw [TorsorArrow.compActualMap]
    simp only [TorsorHom.comp_apply, GTorsorEquiv.symmTorsorHom_apply]
    rw [hflat, hten, hpsi, hcoord]
  rw [hL, hR]
  rw [TorsorArrow.comp_multiplier]
  rw [mul_comm]
/-- The canonical equivariant map `T^⊗1 → T`. -/
def tensorPowerOneTorsorHom (T : GTorsor Fˣ) (i0 : Fin 1) :
    TorsorHom (tensorPowerAt T 1 i0) T where
  toFun := tensorPowerOneEquiv T i0
  map_smul := tensorPowerOneEquiv_smul T i0

theorem TorsorArrow.toTorsorHom_id {D : GlobalPlaceData F} (P : TorsorPresentation D) :
    (TorsorArrow.id P).toTorsorHom =
      tensorPowerOneTorsorHom P.T (tensorPowerAtOfIndex (Nat.one_pos)) := by
  apply TorsorHom.ext
  show (TorsorArrow.id P).toTorsorHom.toFun =
    (tensorPowerOneTorsorHom P.T (tensorPowerAtOfIndex (Nat.one_pos))).toFun
  funext q
  change ((TorsorArrow.id P).toTorsorHom.toFun (q : tensorCarrier P.T 1) :
      P.T.carrier) =
    tensorPowerOneEquiv P.T (tensorPowerAtOfIndex (Nat.one_pos)) q
  have hq : (q : tensorCarrier P.T 1) = tensorPoint P.T 1
      (tensorPowerOneEquiv P.T (tensorPowerAtOfIndex (Nat.one_pos)) q) := by
    conv_lhs => rw [← (tensorPowerOneEquiv P.T
      (tensorPowerAtOfIndex (Nat.one_pos))).symm_apply_apply q]
    rfl
  rw [hq]
  show ((TorsorArrow.id P).toTorsorHom.toFun
      (tensorPoint P.T 1 (tensorPowerOneEquiv P.T
        (tensorPowerAtOfIndex (Nat.one_pos)) q)) : P.T.carrier) =
    (tensorPowerOneEquiv P.T (tensorPowerAtOfIndex (Nat.one_pos))).toFun
      (tensorPoint P.T 1 (tensorPowerOneEquiv P.T
        (tensorPowerAtOfIndex (Nat.one_pos)) q))
  rw [show (TorsorArrow.id P).toTorsorHom.toFun
      (tensorPoint P.T 1 (tensorPowerOneEquiv P.T
        (tensorPowerAtOfIndex (Nat.one_pos)) q)) =
      GTorsor.coordinate P.T P.base
        (tensorPowerOneEquiv P.T (tensorPowerAtOfIndex (Nat.one_pos)) q) • P.base from by
    simp only [TorsorArrow.id, TorsorArrow.toTorsorHom, TorsorHom.ofPoint_toFun,
      tensorPowerAt_coordinate_tensorPoint, pow_one, one_smul]]
  change GTorsor.coordinate P.T P.base
      (tensorPowerOneEquiv P.T (tensorPowerAtOfIndex (Nat.one_pos)) q) • P.base =
    tensorPowerOneEquiv P.T (tensorPowerAtOfIndex (Nat.one_pos))
      (tensorPoint P.T 1 (tensorPowerOneEquiv P.T
        (tensorPowerAtOfIndex (Nat.one_pos)) q))
  rw [tensorPowerOneEquiv_tensorPoint]
  exact GTorsor.coordinate_spec P.T P.base _

/-! ## 5. The base-point caveat: `PresentationIso` is strictly stronger -/

section BasePointCaveat

variable {D : GlobalPlaceData F}

/-- The degree-one arrow of a base-point change: from the standard re-based
presentation `rebase P 1` to `rebase P h`.  Its multiplier is `h⁻¹` (the
`(1,h)` base-point-change arrow of the handoff, in the convention of
`TorsorArrow`). -/
def rebaseDegreeOneArrow (hD : D.HasFiniteSupport) (P : TorsorPresentation D) (h : Fˣ) :
    TorsorArrow (TorsorPresentation.rebase hD P 1) (TorsorPresentation.rebase hD P h) :=
  TorsorArrow.rebaseArrow hD 1 h (TorsorArrow.id P)

@[simp]
theorem rebaseDegreeOneArrow_degree (hD : D.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) :
    (rebaseDegreeOneArrow hD P h).degree = 1 := rfl

@[simp]
theorem rebaseDegreeOneArrow_multiplier (hD : D.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) :
    (rebaseDegreeOneArrow hD P h).multiplier = h⁻¹ := by
  rw [rebaseDegreeOneArrow, TorsorArrow.rebaseArrow_multiplier]
  show h⁻¹ * (TorsorArrow.id P).multiplier * 1 ^ (TorsorArrow.id P).degree = h⁻¹
  rw [show (TorsorArrow.id P).multiplier = 1 from rfl,
    show (TorsorArrow.id P).degree = 1 from rfl]
  simp

/-- The inverse degree-one arrow of the base-point change. -/
def rebaseDegreeOneArrowInverse (hD : D.HasFiniteSupport) (P : TorsorPresentation D)
    (h : Fˣ) :
    TorsorArrow (TorsorPresentation.rebase hD P h) (TorsorPresentation.rebase hD P 1) :=
  TorsorArrow.rebaseArrow hD h 1 (TorsorArrow.id P)

/-- The base-point-change arrows are mutually inverse in the arrow category
(up to the standard re-based presentation `rebase P 1`). -/
theorem rebaseDegreeOneArrow_comp_inverse (hD : D.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) :
    TorsorArrow.comp (rebaseDegreeOneArrow hD P h)
        (rebaseDegreeOneArrowInverse hD P h) =
      TorsorArrow.id (TorsorPresentation.rebase hD P 1) := by
  rw [rebaseDegreeOneArrow, rebaseDegreeOneArrowInverse,
    ← TorsorArrow.rebaseArrow_comp (P₁ := P) (P₂ := P) (P₃ := P) hD 1 h 1
      (TorsorArrow.id P) (TorsorArrow.id P),
    TorsorArrow.comp_id, TorsorArrow.rebaseArrow_id]

theorem rebaseDegreeOneArrow_inverse_comp (hD : D.HasFiniteSupport)
    (P : TorsorPresentation D) (h : Fˣ) :
    TorsorArrow.comp (rebaseDegreeOneArrowInverse hD P h)
        (rebaseDegreeOneArrow hD P h) =
      TorsorArrow.id (TorsorPresentation.rebase hD P h) := by
  rw [rebaseDegreeOneArrow, rebaseDegreeOneArrowInverse,
    ← TorsorArrow.rebaseArrow_comp (P₁ := P) (P₂ := P) (P₃ := P) hD h 1 h
      (TorsorArrow.id P) (TorsorArrow.id P),
    TorsorArrow.comp_id, TorsorArrow.rebaseArrow_id]

/-- A nontrivial base-point change moves the base point (the action is free). -/
theorem rebase_base_ne (hD : D.HasFiniteSupport) (P : TorsorPresentation D)
    {h : Fˣ} (hh : h ≠ 1) :
    (TorsorPresentation.rebase hD P h).base ≠ P.base := by
  intro hbase
  apply hh
  have h1 : h • P.base = P.base := by
    simpa only [TorsorPresentation.rebase] using hbase
  exact P.T.free h P.base h1

/-- A `PresentationIso` has degree one and multiplier one as an arrow. -/
theorem PresentationIso.toArrow_degree {D : GlobalPlaceData F}
    {P Q : TorsorPresentation D} (e : PresentationIso P Q) :
    (PresentationIso.toArrow e).degree = 1 := rfl

theorem PresentationIso.toArrow_multiplier {D : GlobalPlaceData F}
    {P Q : TorsorPresentation D} (e : PresentationIso P Q) :
    (PresentationIso.toArrow e).multiplier = 1 := rfl

/-- **The base-point caveat.**  A nontrivial base-point change is realized by
a degree-one arrow (with multiplier `h⁻¹`, hence invertible in the arrow
category), but it is NOT induced by any `PresentationIso`: presentation
isomorphisms fix the base point and all local points, and their arrows have
multiplier one.  Thus `PresentationIso` is strictly stronger than the class of
invertible arrows. -/
theorem rebaseDegreeOneArrow_not_presentationIso (hD : D.HasFiniteSupport)
    (P : TorsorPresentation D) {h : Fˣ} (hh : h ≠ 1) :
    ¬ ∃ e : PresentationIso (TorsorPresentation.rebase hD P 1)
        (TorsorPresentation.rebase hD P h),
        PresentationIso.toArrow e = rebaseDegreeOneArrow hD P h := by
  rintro ⟨e, he⟩
  have h1 : (rebaseDegreeOneArrow hD P h).multiplier = 1 := by
    rw [← he]
    exact PresentationIso.toArrow_multiplier e
  rw [rebaseDegreeOneArrow_multiplier] at h1
  exact hh (by simpa using congrArg (fun x : Fˣ => x⁻¹) h1)

end BasePointCaveat

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
