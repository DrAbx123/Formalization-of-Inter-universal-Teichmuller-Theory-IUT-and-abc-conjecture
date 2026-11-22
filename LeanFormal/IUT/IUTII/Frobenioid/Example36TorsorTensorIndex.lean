import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTensorPower
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorLocalTensor
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorPresentation

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# Independence of the tensor-power coordinate (III Example 3.6, tensor half)

`Example36TorsorTensorPower` constructs the n-fold contracted product of a
G-torsor T as the quotient of n-tuples by the multiplier relation

  x ~ y  ⟺  ∃ m : Fin n → G, (∀ i, y i = m i • x i) and ∏ i, m i = 1,

and equips it with the residual G-action through a chosen coordinate
`i0 : Fin n`,

  h • [x] = [update x i0 (h • x i0)],

giving the torsor `tensorPowerAt T n i0`.  That file also defines
`tensorPower T n` as the special case where `i0` is the first coordinate.

The present file supplies the missing independence statement needed before the
notation `T^⊗n` may be called canonical: the contracted product and its residual
action do not depend on the choice of `i0` (up to canonical isomorphism, and in
fact the torsor structures coincide because the actions coincide).

Contents:

1. A structure `GTorsorEquiv` of isomorphisms of G-torsors (equivariant
   bijections), with the proved facts that its underlying map is bijective, that
   it preserves torsor coordinates, and that it is determined on coordinates by
   the image of a base point.
2. The permutation action on n-tuples.  Precomposition with the inverse of a
   permutation `σ : Equiv.Perm (Fin n)` preserves the multiplier relation
   (`tensorRel_permute`), hence descends to the quotient (`tensorPermute`).
   The induced map intertwines the residual action at `i0` with the residual
   action at `σ i0` (`tensorPermute_tensorSMul`).
3. **Permutation invariance**: permuting the n coordinates does not change the
   class in the contracted product (`tensorPermute_eq_self`).  The proof uses a
   base point of T and the telescoping of the relative coordinates
   `coordinate t₀ (x i)` along the permutation.
4. The residual action is independent of the coordinate
   (`tensorSMul_independent`), so the identity map is an isomorphism of torsors
   between `tensorPowerAt T n i0` and `tensorPowerAt T n i0'`
   (`tensorPowerAtEquiv`), and the permutation of coordinates is an isomorphism
   between the torsors at `i0` and `σ i0` (`tensorPermuteGTorsorEquiv`).
5. Coordinate compatibility: the coordinate between two tensor points is the
   n-th power of the coordinate in T, for the permuted tensor point as well
   (`tensorPowerAt_coordinate_permute_tensorPoint`), and the torsor coordinate
   function itself does not depend on the chosen residual coordinate
   (`tensorPowerAt_coordinate_independent`).
6. The local tensor point map `phi_n` of `Example36TorsorLocalTensor` for a
   different residual coordinate differs from the original one exactly by the
   permutation action on local contracted products
   (`localTensorPointMap_permute`); the local coordinate `n • a` is
   independent of the coordinate choice
   (`localCoord_localTensorPointMap_independent`).
7. Presentation-level corollary: the tensor-power object attached to a torsor
   presentation is canonically isomorphic for any choice of residual coordinate
   (`tensorPowerAtPresentationEquiv`), so constructions that use the tensor power
   of a presentation's underlying torsor (for instance the degree-n arrow
   realization, which fixes the standard index `0`) do not depend on that choice.

Boundary: this is the tensor-coordinate bookkeeping of the local tensorial half
of III Example 3.6.  It does not construct local Hodge theaters, prime-strips,
the global torsor category, or any identification with source objects.  The
presentation-level statement only compares the tensor powers of the underlying
torsor of one presentation; it does not identify them with source data.  The
permutation action is shown to be the identity on the quotient, so it supplies
well-definedness and equivariance of coordinate changes but no new torsor
structure.
-/

noncomputable section

open scoped BigOperators

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace TensorIndex

open GTorsorTensor

universe u v
variable {G : Type u} [CommGroup G]

/-! ## Isomorphisms of G-torsors -/

/-- An isomorphism of G-torsors: an equivariant bijection.  The inverse is part of
the data, so the isomorphism can be used in both directions without choice. -/
structure GTorsorEquiv (T₁ T₂ : GTorsor G) where
  /-- The underlying map. -/
  toFun : T₁.carrier → T₂.carrier
  /-- The inverse map. -/
  invFun : T₂.carrier → T₁.carrier
  /-- The inverse is a left inverse. -/
  left_inv : ∀ x : T₁.carrier, invFun (toFun x) = x
  /-- The inverse is a right inverse. -/
  right_inv : ∀ y : T₂.carrier, toFun (invFun y) = y
  /-- The map is equivariant for the two G-actions. -/
  map_smul : ∀ (g : G) (x : T₁.carrier), toFun (g • x) = g • toFun x

namespace GTorsorEquiv

variable {T₁ T₂ : GTorsor G}

/-- The underlying map of a torsor isomorphism is bijective. -/
theorem bijective (e : GTorsorEquiv T₁ T₂) : Function.Bijective e.toFun :=
  ⟨fun x y h => by
      have h' : e.invFun (e.toFun x) = e.invFun (e.toFun y) := congrArg e.invFun h
      rwa [e.left_inv x, e.left_inv y] at h',
    fun y => ⟨e.invFun y, e.right_inv y⟩⟩

/-- Coordinates are preserved by every torsor isomorphism. -/
theorem coordinate (e : GTorsorEquiv T₁ T₂) (t x : T₁.carrier) :
    T₂.coordinate (e.toFun t) (e.toFun x) = T₁.coordinate t x := by
  apply GTorsor.coordinate_apply
  rw [← e.map_smul, GTorsor.coordinate_spec]

/-- Coordinate compatibility for a torsor isomorphism, allowing an explicit
description of the image of the base point. -/
theorem coordinate_of_base (e : GTorsorEquiv T₁ T₂) {t₁ : T₁.carrier}
    {t₂ : T₂.carrier} (h : e.toFun t₁ = t₂) (x : T₁.carrier) :
    T₂.coordinate t₂ (e.toFun x) = T₁.coordinate t₁ x := by
  rw [← h]
  exact e.coordinate t₁ x

/-- The identity isomorphism of a torsor. -/
def refl (T : GTorsor G) : GTorsorEquiv T T where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_smul := fun _ _ => rfl

end GTorsorEquiv

/-! ## The permutation action on tensor tuples -/

/-- Precomposition with the inverse of a permutation preserves the multiplier
relation: the multiplier tuple is reindexed, and the product over `Fin n` is
unchanged. -/
theorem tensorRel_permute (T : GTorsor G) (n : ℕ) (σ : Equiv.Perm (Fin n))
    {x y : Fin n → T.carrier} (h : tensorRel T n x y) :
    tensorRel T n (fun i => x (σ.symm i)) (fun i => y (σ.symm i)) := by
  obtain ⟨m, hm, hprod⟩ := h
  refine ⟨fun i => m (σ.symm i), ?_, ?_⟩
  · intro i
    exact hm (σ.symm i)
  · rw [Equiv.prod_comp σ.symm m, hprod]

/-- The permutation action on the quotient: permute the coordinates of a tuple.
Precomposition by `σ.symm` intertwines the residual action at coordinate `i0`
with the residual action at coordinate `σ i0`. -/
def tensorPermute (T : GTorsor G) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    tensorCarrier T n → tensorCarrier T n :=
  Quotient.map (fun x : Fin n → T.carrier => fun i => x (σ.symm i))
    (fun _ _ h => tensorRel_permute T n σ h)

/-- Computation rule for the permutation action on representatives. -/
theorem tensorPermute_mk (T : GTorsor G) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → T.carrier) :
    tensorPermute T σ (Quotient.mk (tensorSetoid T n) x) =
      Quotient.mk (tensorSetoid T n) (fun i => x (σ.symm i)) := by
  rw [tensorPermute, Quotient.map_mk]

/-- The tensor point of a point is fixed by every permutation of the coordinates. -/
theorem tensorPermute_tensorPoint (T : GTorsor G) {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : T.carrier) :
    tensorPermute T σ (tensorPoint T n x) = tensorPoint T n x := by
  rw [tensorPoint, tensorPermute, Quotient.map_mk]

/-- **Permutation invariance of the contracted product**: permuting the n
coordinates of a tuple does not change its class in T^⊗n.  The proof writes each
tuple as `x i = r i • t₀` for a chosen base point `t₀`, telescopes the relative
coordinates `r i * (r (σ.symm i))⁻¹`, and uses that the product is invariant
under the reindexing permutation. -/
theorem tensorPermute_eq_self (T : GTorsor G) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (q : tensorCarrier T n) : tensorPermute T σ q = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [tensorPermute_mk]
    apply Quotient.sound
    change tensorRel T n (fun i => x (σ.symm i)) x
    rw [tensorRel_iff_coordinateProduct_eq_one]
    let t₀ : T.carrier := Classical.choice T.nonempty
    let r : Fin n → G := fun i => T.coordinate t₀ (x i)
    have hbase : ∀ i, x i = r i • t₀ := fun i => (GTorsor.coordinate_spec T t₀ (x i)).symm
    have hcoord : ∀ i, T.coordinate (x (σ.symm i)) (x i) = r i * (r (σ.symm i))⁻¹ := by
      intro i
      rw [hbase i, hbase (σ.symm i), GTorsor.coordinate_basePoint_change,
        GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]
    change ∏ i, T.coordinate (x (σ.symm i)) (x i) = 1
    calc
      ∏ i, T.coordinate (x (σ.symm i)) (x i)
          = ∏ i, r i * (r (σ.symm i))⁻¹ := Finset.prod_congr rfl (fun i _ => hcoord i)
      _ = (∏ i, r i) * ∏ i, (r (σ.symm i))⁻¹ := Finset.prod_mul_distrib
      _ = (∏ i, r i) * (∏ i, r (σ.symm i))⁻¹ := by rw [Finset.prod_inv_distrib]
      _ = (∏ i, r i) * (∏ i, r i)⁻¹ := by rw [Equiv.prod_comp σ.symm r]
      _ = 1 := mul_inv_cancel _

/-- The permutation action is equivariant: permuting by `σ` carries the residual
action at coordinate `i0` to the residual action at coordinate `σ i0`. -/
theorem tensorPermute_tensorSMul (T : GTorsor G) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (i0 : Fin n) (g : G) (q : tensorCarrier T n) :
    tensorPermute T σ (tensorSMul T n i0 g q) =
      tensorSMul T n (σ i0) g (tensorPermute T σ q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [tensorSMul_mk, tensorPermute_mk, tensorPermute_mk, tensorSMul_mk]
    congr 1
    funext i
    by_cases hi : i = σ i0
    · subst hi
      simp
    · rw [Function.update_of_ne hi]
      have hne : σ.symm i ≠ i0 := by
        intro h
        exact hi (by rw [← σ.apply_symm_apply i, h])
      rw [Function.update_of_ne hne]

/-- Concretely, the transposition of two coordinates intertwines the residual
actions at those two coordinates. -/
theorem tensorPermute_swap_tensorSMul (T : GTorsor G) (n : ℕ) (i0 i0' : Fin n)
    (g : G) (q : tensorCarrier T n) :
    tensorPermute T (Equiv.swap i0 i0') (tensorSMul T n i0 g q) =
      tensorSMul T n i0' g (tensorPermute T (Equiv.swap i0 i0') q) := by
  rw [tensorPermute_tensorSMul, Equiv.swap_apply_left]

/-- The residual action of G on the contracted product does not depend on the
chosen coordinate. -/
theorem tensorSMul_independent (T : GTorsor G) (n : ℕ) (i0 i0' : Fin n) (g : G)
    (q : tensorCarrier T n) :
    tensorSMul T n i0 g q = tensorSMul T n i0' g q := by
  have h := tensorPermute_tensorSMul T n (Equiv.swap i0 i0') i0 g q
  rw [Equiv.swap_apply_left] at h
  simpa only [tensorPermute_eq_self] using h

/-! ## Torsor isomorphisms of tensor powers -/

/-- The identity map is an isomorphism between the tensor powers at any two
coordinates: the residual action does not depend on the coordinate. -/
noncomputable def tensorPowerAtEquiv (T : GTorsor G) (n : ℕ) (i0 i0' : Fin n) :
    GTorsorEquiv (tensorPowerAt T n i0) (tensorPowerAt T n i0') where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_smul := fun g x => tensorSMul_independent T n i0 i0' g x

/-- The identity map realizes the canonical isomorphism between the tensor
powers at two coordinates. -/
@[simp]
theorem tensorPowerAtEquiv_toFun (T : GTorsor G) (n : ℕ) (i0 i0' : Fin n) :
    (tensorPowerAtEquiv T n i0 i0').toFun = id := rfl

/-- The permutation-induced isomorphism between the tensor power with the residual
action at coordinate `i0` and the tensor power with the residual action at
coordinate `σ i0`. -/
noncomputable def tensorPermuteGTorsorEquiv (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (σ : Equiv.Perm (Fin n)) :
    GTorsorEquiv (tensorPowerAt T n i0) (tensorPowerAt T n (σ i0)) where
  toFun := tensorPermute T σ
  invFun := tensorPermute T σ.symm
  left_inv := fun q => by
    show tensorPermute T σ.symm (tensorPermute T σ q) = q
    rw [tensorPermute_eq_self, tensorPermute_eq_self]
  right_inv := fun q => by
    show tensorPermute T σ (tensorPermute T σ.symm q) = q
    rw [tensorPermute_eq_self, tensorPermute_eq_self]
  map_smul := fun g x => tensorPermute_tensorSMul T n σ i0 g x

/-- The underlying map of the permutation isomorphism is the permutation of
coordinates. -/
@[simp]
theorem tensorPermuteGTorsorEquiv_toFun (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (σ : Equiv.Perm (Fin n)) :
    (tensorPermuteGTorsorEquiv T n i0 σ).toFun = tensorPermute T σ := rfl

/-- Coordinate compatibility for the permutation isomorphism. -/
theorem tensorPermuteGTorsorEquiv_coordinate (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (σ : Equiv.Perm (Fin n)) (t x : tensorCarrier T n) :
    (tensorPowerAt T n (σ i0)).coordinate (tensorPermute T σ t) (tensorPermute T σ x) =
      (tensorPowerAt T n i0).coordinate t x :=
  GTorsorEquiv.coordinate (tensorPermuteGTorsorEquiv T n i0 σ) t x

/-- The torsor coordinate between two points of the contracted product does not
depend on the chosen residual coordinate. -/
theorem tensorPowerAt_coordinate_independent (T : GTorsor G) (n : ℕ) (i0 i0' : Fin n)
    (t x : tensorCarrier T n) :
    (tensorPowerAt T n i0).coordinate t x =
      (tensorPowerAt T n i0').coordinate t x :=
  (GTorsorEquiv.coordinate (tensorPowerAtEquiv T n i0 i0') t x).symm

/-- **Coordinate law for permuted tensor points**: the coordinate of the permuted
tensor point of `x` relative to the tensor point of `t` is still the n-th power
of the coordinate of `x` relative to `t`. -/
theorem tensorPowerAt_coordinate_permute_tensorPoint (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (σ : Equiv.Perm (Fin n)) (t x : T.carrier) :
    (tensorPowerAt T n (σ i0)).coordinate (tensorPoint T n t)
        (tensorPermute T σ (tensorPoint T n x)) = (T.coordinate t x) ^ n := by
  rw [tensorPermute_tensorPoint, tensorPowerAt_coordinate_tensorPoint]

/-- The coordinate of tensor points does not depend on the chosen coordinate. -/
theorem tensorPowerAt_coordinate_tensorPoint_independent (T : GTorsor G) (n : ℕ)
    (i0 i0' : Fin n) (t x : T.carrier) :
    (tensorPowerAt T n i0).coordinate (tensorPoint T n t) (tensorPoint T n x) =
      (tensorPowerAt T n i0').coordinate (tensorPoint T n t) (tensorPoint T n x) :=
  tensorPowerAt_coordinate_independent T n i0 i0' (tensorPoint T n t) (tensorPoint T n x)

/-! ## The permutation action on local tensor points -/

section LocalTensor

variable {F : Type u} [Field F] {Gamma : Type v} [AddCommGroup Gamma]

open LocalTensorPoint

/-- The permutation of tensor coordinates induces a map on the local contracted
products: the value coordinate is unchanged and the torsor coordinate is
permuted.  It is well defined because the permutation map of the torsor commutes
with the F^x-action (`tensorPermute_tensorSMul`). -/
def localTensorPermute (D : LocalValueData F Gamma) (T : GTorsor Fˣ) (n : ℕ)
    (i0 : Fin n) (σ : Equiv.Perm (Fin n)) :
    LocalContraction D (tensorPowerAt T n i0) →
      LocalContraction D (tensorPowerAt T n (σ i0)) :=
  Quotient.map (fun p : Gamma × tensorCarrier T n => (p.1, tensorPermute T σ p.2)) (by
    intro p q hrel
    obtain ⟨g, rfl⟩ := hrel
    refine ⟨g, ?_⟩
    ext
    · rfl
    · exact tensorPermute_tensorSMul T n σ i0 g p.2)

/-- Computation rule for the permutation action on local contracted products. -/
@[simp]
theorem localTensorPermute_mk (D : LocalValueData F Gamma) (T : GTorsor Fˣ) (n : ℕ)
    (i0 : Fin n) (σ : Equiv.Perm (Fin n)) (a : Gamma) (y : tensorCarrier T n) :
    localTensorPermute D T n i0 σ
        (localContractionMk D (tensorPowerAt T n i0) (a, y)) =
      localContractionMk D (tensorPowerAt T n (σ i0)) (a, tensorPermute T σ y) := by
  rw [localTensorPermute, Quotient.map_mk]

/-- **Relation of the tensor point maps for different coordinates**: the tensor
point map for `σ i0` is the tensor point map for `i0` followed by the permutation
action on local contracted products.  Thus `phi_n` for two coordinate choices
differs exactly by the coordinate permutation; it is not an unknown
identification. -/
theorem localTensorPointMap_permute (D : LocalValueData F Gamma) (T : GTorsor Fˣ)
    (n : ℕ) (i0 : Fin n) (σ : Equiv.Perm (Fin n)) (p : LocalContraction D T) :
    localTensorPointMap D T n (σ i0) p =
      localTensorPermute D T n i0 σ (localTensorPointMap D T n i0 p) := by
  induction p using Quotient.inductionOn with
  | h q =>
    obtain ⟨a, t⟩ := q
    rw [localTensorPointMap_mk]
    rw [localTensorPointMap_mk, localTensorPermute_mk]
    rw [tensorPermute_tensorPoint]

/-- The coordinate of the permuted tensor point map is unchanged: the local
coordinate law `n • a` does not depend on the tensor coordinate. -/
theorem localCoord_localTensorPermute (D : LocalValueData F Gamma) (T : GTorsor Fˣ)
    (n : ℕ) (i0 : Fin n) (σ : Equiv.Perm (Fin n)) (t : T.carrier)
    (p : LocalContraction D (tensorPowerAt T n i0)) :
    localCoord D (tensorPowerAt T n (σ i0)) (tensorPoint T n t)
        (localTensorPermute D T n i0 σ p) =
      localCoord D (tensorPowerAt T n i0) (tensorPoint T n t) p := by
  induction p using Quotient.inductionOn with
  | h q =>
    obtain ⟨a, x⟩ := q
    rw [localTensorPermute_mk, localCoord_mk, localCoord_mk]
    have hcoord : (tensorPowerAt T n (σ i0)).coordinate (tensorPoint T n t)
        (tensorPermute T σ x) =
        (tensorPowerAt T n i0).coordinate (tensorPoint T n t) x := by
      have hbase : (tensorPermuteGTorsorEquiv T n i0 σ).toFun (tensorPoint T n t) =
          tensorPoint T n t := tensorPermute_tensorPoint T σ t
      exact GTorsorEquiv.coordinate_of_base (e := tensorPermuteGTorsorEquiv T n i0 σ)
        (t₁ := tensorPoint T n t) (t₂ := tensorPoint T n t) hbase x
    rw [hcoord]

/-- The local coordinate law for the tensor point map is independent of the
chosen tensor coordinate. -/
theorem localCoord_localTensorPointMap_independent (D : LocalValueData F Gamma)
    (T : GTorsor Fˣ) (n : ℕ) (i0 i0' : Fin n) (t : T.carrier)
    (p : LocalContraction D T) :
    localCoord D (tensorPowerAt T n i0) (tensorPoint T n t)
        (localTensorPointMap D T n i0 p) =
      localCoord D (tensorPowerAt T n i0') (tensorPoint T n t)
        (localTensorPointMap D T n i0' p) := by
  rw [localCoord_localTensorPointMap, localCoord_localTensorPointMap]

end LocalTensor

/-! ## Presentation-level independence of the tensor-power object -/

section Presentation

variable {F : Type u} [Field F] [NumberField F] {D : GlobalPlaceData F}

/-- The tensor-power object used by a torsor presentation is independent of the
chosen residual coordinate: for the underlying torsor `P.T`, the tensor powers at
any two coordinates are canonically isomorphic; the isomorphism is the identity
map on the underlying quotient. -/
noncomputable def tensorPowerAtPresentationEquiv (P : TorsorPresentation D) (n : ℕ)
    (i0 i0' : Fin n) :
    GTorsorEquiv (tensorPowerAt P.T n i0) (tensorPowerAt P.T n i0') :=
  tensorPowerAtEquiv P.T n i0 i0'

/-- The presentation-level isomorphism is realized by the identity map. -/
@[simp]
theorem tensorPowerAtPresentationEquiv_toFun (P : TorsorPresentation D) (n : ℕ)
    (i0 i0' : Fin n) :
    (tensorPowerAtPresentationEquiv (D := D) P n i0 i0').toFun = id := rfl

/-- The presentation-level tensor power at coordinate `i0` is canonically
isomorphic to the one at `σ i0`, through the permutation of the tensor
coordinates. -/
noncomputable def tensorPowerAtPresentationPermuteEquiv (P : TorsorPresentation D)
    (n : ℕ) (i0 : Fin n) (σ : Equiv.Perm (Fin n)) :
    GTorsorEquiv (tensorPowerAt P.T n i0) (tensorPowerAt P.T n (σ i0)) :=
  tensorPermuteGTorsorEquiv P.T n i0 σ

end Presentation

end TensorIndex
end Example36
end LeanFormal.IUT.IUTII.Frobenioid