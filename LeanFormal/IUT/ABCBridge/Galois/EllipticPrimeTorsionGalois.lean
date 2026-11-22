import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.ZMod

/-!
# The prime-`l` torsion subgroup of `E(K)` and its automorphism functoriality

For a field `K` and a Weierstrass curve `E : WeierstrassCurve K`, this file defines the
`l`-torsion subgroup `E[l] = {P : E(K) | l • P = 0}` of the group of nonsingular affine
`K`-points of `E` (`WeierstrassCurve.Affine.Point` with Mathlib's group law), proves that
it is an additive subgroup, and develops the functoriality used by the Frey-curve
Galois-representation chain towards the IUT/ABC reduction.

## Main definitions

* `torsionSubgroup E l`: the `l`-torsion subgroup `E[l]` of `E(K)`.
* `torsionSubgroupMap l f`: restriction of Mathlib's `Point.map` to torsion subgroups.
* `torsionSubgroupEquiv l e`: the torsion-level additive equivalence induced by an
  `S`-algebra equivalence `e : F ≃ₐ[S] K`.
* `galoisPointEquiv W σ`: the action of a `k`-algebra automorphism `σ : K ≃ₐ[k] K` on the
  `K`-points of the base change `W⁄K`.
* `galoisTorsionEquiv W l σ`: the induced group automorphism of `E[l]`.

## Main statements

* `mem_torsionSubgroup`: `P ∈ E[l] ↔ l • P = 0`.
* `map_mem_torsionSubgroup`: Mathlib's `Point.map f` maps torsion into torsion.
* `torsionSubgroupEquiv`: the restriction is an additive equivalence.
* `galoisPointEquiv_mul_apply`, `galoisPointEquiv_one_apply`: the action laws.
* `galoisTorsionEquiv_zmod_smul`: the action is `ZMod l`-linear on `E[l]`.

## The Galois action available at this Mathlib level

Mathlib (this pin) provides point functoriality only for algebra homomorphisms over a
common base ring: `Point.map f : E_F →+ E_K` for `f : F →ₐ[S] K`, where the curve is
defined over a ring `R` with `R → S → F` and `R → S → K` algebra structures.  Accordingly
the Galois action formalized here is the action of the group `K ≃ₐ[k] K` of `k`-algebra
automorphisms of `K` on the group `E(K)` of `K`-points of the curve `W` base changed from
a base field `k` to `K`, i.e. automorphisms of `K` fixing `k`.  For a Galois extension
`K/k` this is the usual Galois action on `K`-points; no profinite Galois group, no Galois
correspondence and no representability of the action is constructed or claimed here.  The
coefficients of `W⁄K` are fixed by every such `σ` (`baseChange_map_toRingHom`), and points
obtained by base change from `k` are fixed by the action (`galoisPointEquiv_baseChange`).

A general ring automorphism `σ : K →+* K` with `(W.map σ) = W` has no point map in this
Mathlib version: point functoriality is only available for algebra homomorphisms over a
common base, so the results here are stated for `σ : K ≃ₐ[k] K`, with the curve visible
over the base field `k`.

## Boundaries (not claimed)

No rank-two, freeness or basis statement for `E[l]`, no `SL₂` image, no Galois
representability and no finiteness of `E[l]` are claimed here.  As in Mathlib's own
`EllipticCurve/Affine/Point.lean`, the group law on affine points carries an explicit
`DecidableEq` instance argument; the statements below carry `[DecidableEq K]` for the
same reason.
-/

namespace LeanFormal.IUT.ABCBridge.Galois

open WeierstrassCurve.Affine
open scoped WeierstrassCurve

noncomputable section

/-! ## The `l`-torsion subgroup -/

section TorsionSubgroup

variable {K : Type*} [Field K] [DecidableEq K]

/-- The `l`-torsion subgroup `E[l] = {P : E(K) | l • P = 0}` of the group of nonsingular
affine `K`-points of a Weierstrass curve `E` over `K`.

For an elliptic curve `E` and a prime `l`, this is the usual prime-`l` torsion subgroup.
No `E.IsElliptic` assumption is needed to define it: the group law on nonsingular points
exists for every Weierstrass curve over a field. -/
def torsionSubgroup (E : WeierstrassCurve K) (l : ℕ) : AddSubgroup (Point E) where
  carrier := {P | l • P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change l • P = 0 at hP
    change l • Q = 0 at hQ
    change l • (P + Q) = 0
    rw [nsmul_add, hP, hQ, add_zero]
  neg_mem' := by
    intro P hP
    change l • P = 0 at hP
    change l • (-P) = 0
    rw [neg_nsmul, hP, neg_zero]

/-- Membership in the `l`-torsion subgroup: `E[l] = {P | l • P = 0}`. -/
@[simp]
theorem mem_torsionSubgroup {E : WeierstrassCurve K} {l : ℕ} {P : Point E} :
    P ∈ torsionSubgroup E l ↔ l • P = 0 :=
  Iff.rfl

/-- If `l ∣ m` then the `l`-torsion subgroup is contained in the `m`-torsion subgroup. -/
theorem torsionSubgroup_mono {E : WeierstrassCurve K} {l m : ℕ} (h : l ∣ m) :
    torsionSubgroup E l ≤ torsionSubgroup E m := by
  intro P hP
  change l • P = 0 at hP
  change m • P = 0
  obtain ⟨d, rfl⟩ := h
  rw [mul_nsmul, hP, nsmul_zero]

/-- The canonical `ZMod l`-module structure on the `l`-torsion subgroup, induced by
`l • P = 0` for `P ∈ E[l]` (`AddCommGroup.zmodModule`). -/
noncomputable instance torsionSubgroup_zmodModule (E : WeierstrassCurve K) (l : ℕ) :
    Module (ZMod l) (torsionSubgroup E l) :=
  AddCommGroup.zmodModule (n := l) fun x =>
    Subtype.ext (show l • ((x : torsionSubgroup E l) : Point E) = 0 from
      mem_torsionSubgroup.mp x.2)

end TorsionSubgroup

/-! ## Functoriality of torsion subgroups -/

section Functoriality

variable {R : Type*} {S : Type*} {F : Type*} {K : Type*}
  [CommRing R] [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [Algebra R K] [Algebra S K] [IsScalarTower R S K]

/-- The identity algebra homomorphism acts trivially on points; this generalizes
Mathlib's `WeierstrassCurve.Affine.Point.map_id` from `Algebra.ofId F F` to
`AlgHom.id S F`. -/
theorem map_algHom_id {W' : WeierstrassCurve R} (P : Point (W'⁄F)) :
    Point.map (AlgHom.id S F) P = P := by
  cases P with
  | zero => exact Point.map_zero (AlgHom.id S F)
  | some x y h =>
      rw [Point.map_some]
      rfl

/-- Mathlib's `Point.map f`, restricted to torsion subgroups: it sends `E_F[l]` into
`E_K[l]`. -/
theorem map_mem_torsionSubgroup {W' : WeierstrassCurve R} (l : ℕ) (f : F →ₐ[S] K)
    {P : Point (W'⁄F)} (hP : P ∈ torsionSubgroup (W'⁄F) l) :
    Point.map f P ∈ torsionSubgroup (W'⁄K) l := by
  rw [mem_torsionSubgroup] at hP ⊢
  rw [← (Point.map f).map_nsmul l P, hP, (Point.map f).map_zero]

/-- The restriction of Mathlib's `Point.map f` to the `l`-torsion subgroups, as an
additive homomorphism `E_F[l] →+ E_K[l]`. -/
def torsionSubgroupMap {W' : WeierstrassCurve R} (l : ℕ) (f : F →ₐ[S] K) :
    torsionSubgroup (W'⁄F) l →+ torsionSubgroup (W'⁄K) l where
  toFun P := ⟨Point.map f ↑P, map_mem_torsionSubgroup l f P.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by simp)

/-- The underlying point of `torsionSubgroupMap l f P` is `Point.map f` of the underlying
point. -/
@[simp]
theorem torsionSubgroupMap_coe {W' : WeierstrassCurve R} (l : ℕ) (f : F →ₐ[S] K)
    (P : torsionSubgroup (W'⁄F) l) :
    ((torsionSubgroupMap l f P : torsionSubgroup (W'⁄K) l) : Point (W'⁄K)) =
      Point.map f ↑P :=
  rfl

/-- `torsionSubgroupMap` is functorial in the identity algebra homomorphism. -/
theorem torsionSubgroupMap_id {W' : WeierstrassCurve R} (l : ℕ) :
    torsionSubgroupMap (W' := W') l (AlgHom.id S F) =
      AddMonoidHom.id (torsionSubgroup (W'⁄F) l) := by
  ext P
  simp only [torsionSubgroupMap_coe, AddMonoidHom.id_apply]
  exact map_algHom_id (P := (↑P : Point (W'⁄F)))

/-- `torsionSubgroupMap` is functorial in composition of algebra homomorphisms. -/
theorem torsionSubgroupMap_comp {W' : WeierstrassCurve R} (l : ℕ) {L : Type*}
    [Field L] [DecidableEq L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (f : F →ₐ[S] K) (g : K →ₐ[S] L) :
    torsionSubgroupMap (W' := W') l (g.comp f) =
      (torsionSubgroupMap (W' := W') l g).comp (torsionSubgroupMap (W' := W') l f) := by
  ext P
  simp only [torsionSubgroupMap_coe, AddMonoidHom.comp_apply, Point.map_map]

/-- `Point.map` along an `S`-algebra equivalence `e : F ≃ₐ[S] K` is an additive
equivalence on points, with inverse induced by `e.symm`. -/
def pointAlgEquiv {W' : WeierstrassCurve R} (e : F ≃ₐ[S] K) :
    Point (W'⁄F) ≃+ Point (W'⁄K) where
  toFun := Point.map e.toAlgHom
  invFun := Point.map e.symm.toAlgHom
  left_inv P := by
    rw [Point.map_map]
    rw [show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id S F from
      AlgHom.ext fun x => by simp]
    exact map_algHom_id P
  right_inv P := by
    rw [Point.map_map]
    rw [show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id S K from
      AlgHom.ext fun x => by simp]
    exact map_algHom_id P
  map_add' := (Point.map e.toAlgHom).map_add

@[simp]
theorem pointAlgEquiv_apply {W' : WeierstrassCurve R} (e : F ≃ₐ[S] K)
    (P : Point (W'⁄F)) :
    pointAlgEquiv e P = Point.map e.toAlgHom P :=
  rfl

/-- The restriction of an algebra equivalence to the `l`-torsion subgroups, as an
additive equivalence `E_F[l] ≃+ E_K[l]`. -/
def torsionSubgroupEquiv {W' : WeierstrassCurve R} (l : ℕ) (e : F ≃ₐ[S] K) :
    torsionSubgroup (W'⁄F) l ≃+ torsionSubgroup (W'⁄K) l where
  toFun := torsionSubgroupMap l e.toAlgHom
  invFun := torsionSubgroupMap l e.symm.toAlgHom
  left_inv P := by
    apply Subtype.ext
    simp only [torsionSubgroupMap_coe]
    rw [Point.map_map]
    rw [show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id S F from
      AlgHom.ext fun x => by simp]
    exact map_algHom_id (P := (↑P : Point (W'⁄F)))
  right_inv P := by
    apply Subtype.ext
    simp only [torsionSubgroupMap_coe]
    rw [Point.map_map]
    rw [show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id S K from
      AlgHom.ext fun x => by simp]
    exact map_algHom_id (P := (↑P : Point (W'⁄K)))
  map_add' := map_add (torsionSubgroupMap l e.toAlgHom)

@[simp]
theorem torsionSubgroupEquiv_coe {W' : WeierstrassCurve R} (l : ℕ) (e : F ≃ₐ[S] K)
    (P : torsionSubgroup (W'⁄F) l) :
    ((torsionSubgroupEquiv l e P : torsionSubgroup (W'⁄K) l) : Point (W'⁄K)) =
      Point.map e.toAlgHom ↑P :=
  rfl

/-- `Point.map` is `ZMod l`-linear on the `l`-torsion subgroups. -/
theorem torsionSubgroupMap_zmod_smul {W' : WeierstrassCurve R} (l : ℕ) (f : F →ₐ[S] K)
    (c : ZMod l) (P : torsionSubgroup (W'⁄F) l) :
    torsionSubgroupMap l f (c • P) = c • torsionSubgroupMap l f P :=
  ZMod.map_smul (torsionSubgroupMap l f) c P

end Functoriality

/-! ## The action of `k`-algebra automorphisms of `K` -/

section GaloisAction

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K] [DecidableEq K]

/-- The action of a `k`-algebra automorphism `σ` of `K` on the `K`-points of the base
change `W⁄K` of a Weierstrass curve `W` over `k`: this is Mathlib's `Point.map σ.toAlgHom`
with source and target both `W⁄K`. -/
def galoisPointEquiv (W : WeierstrassCurve k) (σ : K ≃ₐ[k] K) :
    Point (W⁄K) ≃+ Point (W⁄K) :=
  pointAlgEquiv (W' := W) (R := k) (S := k) (F := K) (K := K) σ

@[simp]
theorem galoisPointEquiv_apply (W : WeierstrassCurve k) (σ : K ≃ₐ[k] K)
    (P : Point (W⁄K)) :
    galoisPointEquiv W σ P = Point.map σ.toAlgHom P :=
  rfl

/-- The induced group automorphism of the `l`-torsion subgroup `E[l]`. -/
def galoisTorsionEquiv (W : WeierstrassCurve k) (l : ℕ) (σ : K ≃ₐ[k] K) :
    torsionSubgroup (W⁄K) l ≃+ torsionSubgroup (W⁄K) l :=
  torsionSubgroupEquiv (W' := W) (R := k) (S := k) (F := K) (K := K) l σ

@[simp]
theorem galoisTorsionEquiv_coe (W : WeierstrassCurve k) (l : ℕ) (σ : K ≃ₐ[k] K)
    (P : torsionSubgroup (W⁄K) l) :
    ((galoisTorsionEquiv W l σ P : torsionSubgroup (W⁄K) l) : Point (W⁄K)) =
      Point.map σ.toAlgHom ↑P :=
  rfl

omit [DecidableEq K] in
/-- The coercion to algebra homomorphisms of a product of `k`-algebra equivalences of
`K` is the composition of the coerced algebra homomorphisms. -/
theorem algEquiv_mul_toAlgHom (σ τ : K ≃ₐ[k] K) :
    (↑(σ * τ) : K →ₐ[k] K) = σ.toAlgHom.comp τ.toAlgHom := by
  ext x
  simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using AlgEquiv.mul_apply σ τ x

/-- Composition law for the action on points. -/
theorem galoisPointEquiv_mul_apply (W : WeierstrassCurve k) (σ τ : K ≃ₐ[k] K)
    (P : Point (W⁄K)) :
    galoisPointEquiv W (σ * τ) P = galoisPointEquiv W σ (galoisPointEquiv W τ P) := by
  rw [galoisPointEquiv_apply, galoisPointEquiv_apply, galoisPointEquiv_apply]
  rw [Point.map_map]
  rw [algEquiv_mul_toAlgHom]

/-- The identity acts trivially on points. -/
theorem galoisPointEquiv_one_apply (W : WeierstrassCurve k) (P : Point (W⁄K)) :
    galoisPointEquiv W (1 : K ≃ₐ[k] K) P = P := by
  rw [galoisPointEquiv_apply]
  have h : (↑(1 : K ≃ₐ[k] K) : K →ₐ[k] K) = AlgHom.id k K := by
    rw [show (1 : K ≃ₐ[k] K) = AlgEquiv.refl from rfl]
    exact AlgEquiv.refl_toAlgHom
  rw [h]
  exact map_algHom_id P

/-- The identity acts as the identity additive equivalence. -/
theorem galoisPointEquiv_one (W : WeierstrassCurve k) :
    galoisPointEquiv W (1 : K ≃ₐ[k] K) = AddEquiv.refl (Point (W⁄K)) := by
  ext P
  rw [galoisPointEquiv_one_apply]
  rfl

/-- The `l`-torsion subgroup is stable under the action: the closure lemma at point
level. -/
theorem galoisPointEquiv_mem_torsionSubgroup (W : WeierstrassCurve k) (l : ℕ)
    (σ : K ≃ₐ[k] K) {P : Point (W⁄K)} (hP : P ∈ torsionSubgroup (W⁄K) l) :
    galoisPointEquiv W σ P ∈ torsionSubgroup (W⁄K) l := by
  simpa only [galoisPointEquiv_apply] using
    map_mem_torsionSubgroup (W' := W) l σ.toAlgHom hP

/-- Composition law for the action on the torsion subgroup. -/
theorem galoisTorsionEquiv_mul_apply (W : WeierstrassCurve k) (l : ℕ) (σ τ : K ≃ₐ[k] K)
    (P : torsionSubgroup (W⁄K) l) :
    galoisTorsionEquiv W l (σ * τ) P =
      galoisTorsionEquiv W l σ (galoisTorsionEquiv W l τ P) := by
  apply Subtype.ext
  simp only [galoisTorsionEquiv_coe]
  simpa only [galoisPointEquiv_apply] using galoisPointEquiv_mul_apply W σ τ ↑P

/-- The identity acts trivially on the torsion subgroup. -/
theorem galoisTorsionEquiv_one_apply (W : WeierstrassCurve k) (l : ℕ)
    (P : torsionSubgroup (W⁄K) l) :
    galoisTorsionEquiv W l (1 : K ≃ₐ[k] K) P = P := by
  apply Subtype.ext
  simp only [galoisTorsionEquiv_coe]
  simpa only [galoisPointEquiv_apply] using
    galoisPointEquiv_one_apply W (↑P : Point (W⁄K))

/-- The action is `ZMod l`-linear on the torsion subgroup `E[l]`. -/
theorem galoisTorsionEquiv_zmod_smul (W : WeierstrassCurve k) (l : ℕ) (σ : K ≃ₐ[k] K)
    (c : ZMod l) (P : torsionSubgroup (W⁄K) l) :
    galoisTorsionEquiv W l σ (c • P) = c • galoisTorsionEquiv W l σ P :=
  ZMod.map_smul (galoisTorsionEquiv W l σ).toAddMonoidHom c P

omit [DecidableEq K] in
/-- Coefficient compatibility: pushing the base-changed curve `W⁄K` forward along
`σ : K →+* K` returns the same curve, i.e. the automorphism fixes the coefficients of
`W⁄K`. -/
theorem baseChange_map_toRingHom (W : WeierstrassCurve k) (σ : K ≃ₐ[k] K) :
    (W⁄K).map σ.toRingHom = W⁄K := by
  change (W.map (algebraMap k K)).map σ.toRingHom = W.map (algebraMap k K)
  rw [WeierstrassCurve.map_map]
  congr 1
  ext c
  exact σ.toAlgHom.commutes c

/-- Points that come from `k` by base change are fixed by the action; this is the
compatibility of the action with the rational points. -/
theorem galoisPointEquiv_baseChange (W : WeierstrassCurve k) [DecidableEq k]
    (σ : K ≃ₐ[k] K) (P : Point (W⁄k)) :
    galoisPointEquiv W σ (Point.baseChange k K P) = Point.baseChange k K P := by
  rw [galoisPointEquiv_apply]
  exact Point.map_baseChange (W' := W) (F := k) (K := K) (L := K) σ.toAlgHom P

end GaloisAction

end

end LeanFormal.IUT.ABCBridge.Galois
