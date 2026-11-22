import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# S2074: the geometric fiber functor is FintypeCat-valued, and the curve
etale fundamental group is profinite

Task S2069 shortest path S1, actual (non-card) version.  The file proves the
three items of S1 for the actual geometric fiber functor
`geometricFiberFunctor` of
`LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean`:

1. **M2 (finiteness of the geometric fiber).**
   `geometricFiberObject_finite`: for a field `Ω`, a geometric point
   `x : Spec Ω ⟶ X` and a finite etale cover `Y ⟶ X`, the type of lifts
   `{ s : Spec Ω ⟶ Y // s ≫ (Y ⟶ X) = x }` is finite.

   Proof (no separably closedness of `Ω` is needed).  Form the scheme
   pullback `Z = Y ×_X Spec Ω`; it is affine because `Y ⟶ X` is finite
   (hence affine) and `Spec Ω` is affine.  Let `A = Γ(Z, ⊤)`.  Since
   `Z ⟶ Spec Ω` is finite, `A` is a finite `Ω`-module.  Lifts of `x`
   to `Y` are sections of `Z ⟶ Spec Ω` over `Spec Ω`; under the canonical
   affine isomorphism `Z ≅ Spec A` they are `Ω`-algebra homomorphisms
   `A →ₐ[Ω] Ω`.  Mathlib's
   `Finite (S →ₐ[R] K)` instance (for `Module.Finite R S` and `K` a
   field) then gives the result.  The map from lifts to algebra homs is
   injective (it is postcomposition with the isomorphism `Z ≅ Spec A`).

   The proof actually only uses `IsFinite (Y ⟶ X)`, not `Etale`.

2. **The FintypeCat-valued geometric fiber functor.**
   `geometricFiberFunctorFintype Ω x : FiniteEtaleCover X ⥤ FintypeCat.{u}`,
   with `geometricFiberFunctorFintype_comp_incl` stating that composing with
   `FintypeCat.incl` recovers the existing Type-valued
   `geometricFiberFunctor Ω x`.  The equality is definitional.

3. **The profinite structure.**
   `curveEtaleFundamentalGroupAutEquiv` is the multiplicative equivalence
   `Aut (geometricFiberFunctorFintype Ω x) ≃* curveEtaleFundamentalGroup Ω x`
   obtained from the fully faithful functor `FintypeCat.incl` (via
   `Functor.FullyFaithful.autMulEquivOfFullyFaithful` applied to the
   whiskering of `FintypeCat.incl`; `FintypeCat.incl` is `Full` and
   `Faithful`).

   The Type-valued automorphism group is then given the transported profinite
   topology (`curveEtaleFundamentalGroupTopology`), it is a topological group
   (`curveEtaleFundamentalGroupIsTopologicalGroup`), and
   `curveEtaleFundamentalGroupHomeomorph` is a topological group isomorphism
   `Aut (geometricFiberFunctorFintype Ω x) ≃ₜ* curveEtaleFundamentalGroup Ω x`.
   Finally `curveEtaleFundamentalGroupProfinite` is the actual Mathlib
   `ProfiniteGrp` built from `ProfiniteGrp.of (Aut (geometricFiberFunctorFintype Ω x))`
   and `ProfiniteGrp.ofContinuousMulEquiv`; its underlying type is exactly
   the old `curveEtaleFundamentalGroup Ω x` (definition unchanged, see
   `curveEtaleFundamentalGroupProfinite_coe`).

## Honest boundary

* The theorem `autEquivAutWhiskerRight` of
  `Mathlib.CategoryTheory.Galois.Topology` cannot be applied directly to
  `FintypeCat.incl`: it requires an endofunctor `FintypeCat ⥤ FintypeCat`,
  whereas `FintypeCat.incl : FintypeCat ⥤ Type`.  The compatibility with the
  Type-valued fiber functor is therefore obtained from the *multiplicative*
  part of the same construction, `Functor.FullyFaithful.autMulEquivOfFullyFaithful`
  applied to the whiskering of `incl` (which is fully faithful because
  `incl` is `Full` and `Faithful`).  The topological/profinite structure
  is transported along this group isomorphism.

* No `axiom`, `sorry`, `Nonempty` wrapper or fake data is used.  The only
  classical inputs are the standard `Classical.choice` used by Mathlib
  (e.g. in `Spec.homEquiv`).

## References

* `LeanFormal/IUT/Foundations/Geometry/CurveEtaleFundamentalGroup.lean`
* `LeanFormal/IUT/IUTII/Frobenioid/Example36CurveGaloisCategory.lean`
* `coord/reports/S2069-curve-pi1-inventory.md` §4-5
* `Mathlib/CategoryTheory/FintypeCat.lean` (incl Full/Faithful)
* `Mathlib/CategoryTheory/Galois/Topology.lean` (Aut is a profinite space)
* `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean` (`ProfiniteGrp.of`)
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.Foundations.Geometry

namespace LeanFormal.IUT.XiFPaper.S2074CurveFiberFintypeActual

universe u

/-! ## 1. M2: geometric fibers of finite etale covers are finite -/

/-- **M2.**  The geometric fiber of a finite etale cover at a geometric point
is finite.

The proof does not need `Ω` to be separably closed (and does not need the
cover to be etale): it only uses finiteness of the structure morphism. -/
theorem geometricFiberObject_finite {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    {x : Spec (CommRingCat.of Ω) ⟶ X} (Y : FiniteEtaleCover X) :
    Finite (geometricFiberObject Ω x Y) := by
  -- the structure morphism of the cover and the pullback along the
  -- geometric point
  let f : finiteEtaleCoverScheme Y ⟶ X := finiteEtaleCoverStructure Y
  haveI hf : IsFinite f := Y.2.2
  let Z : Scheme.{u} := pullback f x
  let snd : Z ⟶ Spec (CommRingCat.of Ω) := pullback.snd f x
  haveI hsnd : IsFinite snd := inferInstance
  -- the fiber product is affine because f is finite (hence affine) and the
  -- base is affine
  haveI hZaff : IsAffine Z := isAffine_of_isAffineHom snd
  -- global sections of the fiber product
  let A : CommRingCat.{u} := Γ(Z, ⊤)
  -- the algebra structure Ω → A induced by the projection Z ⟶ Spec Ω,
  -- expressed through the canonical affine isomorphism Z ≅ Spec A
  let ψ : CommRingCat.of Ω ⟶ A := Spec.preimage (Z.isoSpec.inv ≫ snd)
  have hψ : Spec.map ψ = Z.isoSpec.inv ≫ snd := Spec.map_preimage _
  letI alg : Algebra Ω A := ψ.hom.toAlgebra
  -- A is a finite Ω-module
  have hfinψ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    exact inferInstance
  haveI hfinA : Module.Finite Ω A := (RingHom.finite_algebraMap).mp hfinψ
  -- Mathlib: finitely many algebra homomorphisms from a finite algebra to a
  -- field
  haveI : Finite (A →ₐ[Ω] Ω) := inferInstance
  -- a lift of x gives a section of Z ⟶ Spec Ω, hence an Ω-algebra hom A → Ω
  let T : geometricFiberObject Ω x Y → (Spec (CommRingCat.of Ω) ⟶ Z) := fun s =>
    pullback.lift s.1 (𝟙 _) (by simpa using s.2)
  have hT_snd : ∀ s, T s ≫ snd = 𝟙 _ := fun s => pullback.lift_snd _ _ _
  have hT_fst : ∀ s, T s ≫ pullback.fst f x = s.1 := fun s => pullback.lift_fst _ _ _
  let toAlgHom : geometricFiberObject Ω x Y → (A →ₐ[Ω] Ω) := fun s =>
    let φ : A ⟶ CommRingCat.of Ω := Spec.preimage (T s ≫ Z.isoSpec.hom)
    { φ.hom with
      commutes' := by
        intro r
        have hcomp : ψ ≫ φ = 𝟙 (CommRingCat.of Ω) := by
          have h1 : ψ ≫ φ =
              Spec.preimage ((T s ≫ Z.isoSpec.hom) ≫ (Z.isoSpec.inv ≫ snd)) := by
            rw [Spec.preimage_comp]
          rw [h1]
          have h2 : (T s ≫ Z.isoSpec.hom) ≫ (Z.isoSpec.inv ≫ snd) = 𝟙 _ := by
            rw [Category.assoc, Iso.hom_inv_id_assoc]
            exact hT_snd s
          rw [h2, Spec.preimage_id]
        have h3 := congrArg (fun (k : CommRingCat.of Ω ⟶ CommRingCat.of Ω) => k.hom r) hcomp
        change φ.hom (ψ.hom r) = r
        simpa only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply,
          RingHom.id_apply] using h3 }
  -- the lift is recovered from its algebra homomorphism
  refine Finite.of_injective toAlgHom ?_
  intro s s' h
  have hφ' : (Spec.preimage (T s ≫ Z.isoSpec.hom)).hom =
      (Spec.preimage (T s' ≫ Z.isoSpec.hom)).hom := by
    have h' := congrArg (fun k : A →ₐ[Ω] Ω => (k : A →+* Ω)) h
    simpa [toAlgHom] using h'
  have hφ : Spec.preimage (T s ≫ Z.isoSpec.hom) =
      Spec.preimage (T s' ≫ Z.isoSpec.hom) := CommRingCat.hom_ext hφ'
  have hT : T s ≫ Z.isoSpec.hom = T s' ≫ Z.isoSpec.hom := by
    simpa only [Spec.map_preimage] using congrArg Spec.map hφ
  have hT' : T s = T s' := by
    calc T s = (T s ≫ Z.isoSpec.hom) ≫ Z.isoSpec.inv := by simp
      _ = (T s' ≫ Z.isoSpec.hom) ≫ Z.isoSpec.inv := by rw [hT]
      _ = T s' := by simp
  have hs : s.1 = s'.1 := by
    have h1 := congrArg (fun k => k ≫ pullback.fst f x) hT'
    simpa [hT_fst s, hT_fst s'] using h1
  exact Subtype.ext hs

/-- Instance form of M2, so that `FintypeCat.of` can be applied to geometric
fibers. -/
instance geometricFiberObject_finite_inst {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) (Y : FiniteEtaleCover X) :
    Finite (geometricFiberObject Ω x Y) :=
  geometricFiberObject_finite Y

/-! ## 2. The FintypeCat-valued geometric fiber functor -/

/-- The geometric fiber functor at a geometric point, valued in finite types.
Objectwise it is the actual geometric fiber `geometricFiberObject`; the
finiteness instance is M2 above. -/
noncomputable def geometricFiberFunctorFintype {X : Scheme.{u}} (Ω : Type u) [Field Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) :
    FiniteEtaleCover X ⥤ FintypeCat.{u} where
  obj Y := FintypeCat.of (geometricFiberObject Ω x Y)
  map f := FintypeCat.homMk (fun s => geometricFiberMap f s)
  map_id Y := by
    ext s
    rfl
  map_comp f g := by
    ext s
    rfl

/-- Composing the FintypeCat-valued geometric fiber functor with
`FintypeCat.incl` gives exactly the existing Type-valued geometric fiber
functor.  The equality is definitional. -/
theorem geometricFiberFunctorFintype_comp_incl {X : Scheme.{u}} (Ω : Type u) [Field Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) :
    geometricFiberFunctorFintype Ω x ⋙ FintypeCat.incl = geometricFiberFunctor Ω x :=
  rfl

/-- Mathlib's topological `autEquivAutWhiskerRight` for a fully faithful
**endofunctor** `G` of `FintypeCat`: whiskering along `G` gives a
topological group isomorphism of the automorphism groups of the
FintypeCat-valued geometric fiber functor.

This is recorded for completeness.  It cannot be applied to
`FintypeCat.incl` itself, because `autEquivAutWhiskerRight` requires
`G : FintypeCat ⥤ FintypeCat` while `FintypeCat.incl : FintypeCat ⥤ Type`.
For `incl` the multiplicative part is used instead; see
`curveEtaleFundamentalGroupAutEquiv` and
`curveEtaleFundamentalGroupHomeomorph`. -/
noncomputable def geometricFiberFunctorFintype_autEquivAutWhiskerRight {X : Scheme.{u}}
    (Ω : Type u) [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (G : FintypeCat.{u} ⥤ FintypeCat.{u}) (hG : G.FullyFaithful) :
    Aut (geometricFiberFunctorFintype Ω x) ≃ₜ*
      Aut (geometricFiberFunctorFintype Ω x ⋙ G) :=
  PreGaloisCategory.autEquivAutWhiskerRight (F := geometricFiberFunctorFintype Ω x) (G := G) hG

/-! ## 3. Compatibility with the Type-valued fiber functor -/

/-- The multiplicative equivalence between the automorphism group of the
FintypeCat-valued geometric fiber functor and the existing Type-valued
`curveEtaleFundamentalGroup`.

It is obtained from the fully faithful functor `FintypeCat.incl`: whiskering
along it is an equivalence on natural transformations, hence on automorphism
groups.  No topology is involved here. -/
noncomputable def curveEtaleFundamentalGroupAutEquiv {X : Scheme.{u}} (Ω : Type u) [Field Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) :
    Aut (geometricFiberFunctorFintype Ω x) ≃*
      curveEtaleFundamentalGroup (X := X) Ω x := by
  have hFF : ((Functor.whiskeringRight (FiniteEtaleCover X) FintypeCat.{u} (Type u)).obj
      FintypeCat.incl).FullyFaithful :=
    Functor.FullyFaithful.whiskeringRight
      (Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl) (FiniteEtaleCover X)
  let e := hFF.autMulEquivOfFullyFaithful (geometricFiberFunctorFintype Ω x)
  have e' : Aut (geometricFiberFunctorFintype Ω x) ≃*
      Aut (geometricFiberFunctorFintype Ω x ⋙ FintypeCat.incl) := e
  rw [geometricFiberFunctorFintype_comp_incl] at e'
  exact e'

/-! ## 4. The profinite structure on the etale fundamental group -/

/-- The profinite topology on the Type-valued geometric fiber automorphism
group, transported from the Mathlib profinite topology on
`Aut (geometricFiberFunctorFintype Ω x)` along the group isomorphism above.
This does not change the definition of `curveEtaleFundamentalGroup`. -/
noncomputable instance curveEtaleFundamentalGroupTopology {X : Scheme.{u}} (Ω : Type u)
    [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ X) :
    TopologicalSpace (curveEtaleFundamentalGroup (X := X) Ω x) :=
  TopologicalSpace.induced (curveEtaleFundamentalGroupAutEquiv Ω x).symm inferInstance

/-- The continuous multiplicative equivalence between the FintypeCat-valued
fiber functor automorphism group (with Mathlib's profinite topology) and the
Type-valued `curveEtaleFundamentalGroup` (with the transported topology). -/
noncomputable def curveEtaleFundamentalGroupHomeomorph {X : Scheme.{u}} (Ω : Type u)
    [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ X) :
    Aut (geometricFiberFunctorFintype Ω x) ≃ₜ*
      curveEtaleFundamentalGroup (X := X) Ω x where
  __ := curveEtaleFundamentalGroupAutEquiv Ω x
  continuous_toFun := by
    rw [continuous_induced_rng]
    simpa using continuous_id
  continuous_invFun := by
    exact continuous_induced_dom

/-- The transported topology makes `curveEtaleFundamentalGroup` a
topological group. -/
noncomputable instance curveEtaleFundamentalGroupIsTopologicalGroup {X : Scheme.{u}}
    (Ω : Type u) [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ X) :
    IsTopologicalGroup (curveEtaleFundamentalGroup (X := X) Ω x) :=
  (curveEtaleFundamentalGroupHomeomorph Ω x).symm.isTopologicalGroup

/-- **The profinite curve etale fundamental group.**

This is the Mathlib `ProfiniteGrp` attached to
`ProfiniteGrp.of (Aut (geometricFiberFunctorFintype Ω x))`, transported to the
Type-valued `curveEtaleFundamentalGroup` along the continuous multiplicative
equivalence.  Its underlying type is exactly `curveEtaleFundamentalGroup Ω x`
(see `curveEtaleFundamentalGroupProfinite_coe`); the original definition
`Aut (geometricFiberFunctor Ω x)` is not changed. -/
noncomputable def curveEtaleFundamentalGroupProfinite {X : Scheme.{u}} (Ω : Type u)
    [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ X) :
    ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.ofContinuousMulEquiv
    (G := ProfiniteGrp.of (Aut (geometricFiberFunctorFintype Ω x)))
    (curveEtaleFundamentalGroupHomeomorph Ω x)

/-- The underlying type of the profinite group is the old
`curveEtaleFundamentalGroup`, definitionally. -/
theorem curveEtaleFundamentalGroupProfinite_coe {X : Scheme.{u}} (Ω : Type u) [Field Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) :
    (curveEtaleFundamentalGroupProfinite Ω x : Type (u + 1)) =
      curveEtaleFundamentalGroup (X := X) Ω x :=
  rfl

/-- The profinite group is isomorphic, as a profinite group, to the
`ProfiniteGrp.of (Aut F)` of the FintypeCat-valued fiber functor. -/
noncomputable def curveEtaleFundamentalGroupProfiniteIso {X : Scheme.{u}} (Ω : Type u)
    [Field Ω] (x : Spec (CommRingCat.of Ω) ⟶ X) :
    ProfiniteGrp.of (Aut (geometricFiberFunctorFintype Ω x)) ≅
      curveEtaleFundamentalGroupProfinite Ω x :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso (curveEtaleFundamentalGroupHomeomorph Ω x)

/-! ## 5. Axiom audit -/

#print axioms geometricFiberObject_finite
#print axioms geometricFiberFunctorFintype_comp_incl
#print axioms geometricFiberFunctorFintype_autEquivAutWhiskerRight
#print axioms curveEtaleFundamentalGroupAutEquiv
#print axioms curveEtaleFundamentalGroupProfinite
#print axioms curveEtaleFundamentalGroupProfiniteIso

end LeanFormal.IUT.XiFPaper.S2074CurveFiberFintypeActual
