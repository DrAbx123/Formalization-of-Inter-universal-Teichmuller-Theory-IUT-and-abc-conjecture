import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Clopen finite subschemes and affine finite-group quotient infrastructure

This file contains two compiled infrastructure layers for the finite etale clopen
complement construction.

## Clopen finiteness

The inclusion of a clopen open subscheme is an open immersion whose range is closed,
hence a closed immersion by IsClosedImmersion.of_isPreimmersion; closed immersions are
finite, and finiteness is stable under composition. This gives finiteness of the
structure morphism of a clopen open subscheme over a base over which the ambient scheme
is finite.

## Finite-group quotient interface

Affine fixed points and the induced affine quotient map, together with the abstract
coproduct/coequalizer description of colimits indexed by a one-object group category.

## Gluing plan (not formalized here)

To pass from the affine quotient to a scheme quotient one would choose a G-invariant
affine open cover of the scheme, take the affine quotients Spec(B_i^G), and glue the
pieces along the affine quotient maps on invariant intersections, then verify finite
etale descent and the universal property in Over S.  Only the affine invariant map and
the categorical colimit interface are compiled here; the gluing and the scheme-theoretic
finite etale quotient theorem are not formalized, and no card or placeholder is used for
them.

All declarations are actual compiled lemmas; no cards or placeholders are introduced.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace LeanFormal.IUT.Foundations.Geometry
namespace ClopenFiniteComplement

universe u v w

section ClopenFinite

theorem ringHomFinite_algebraMap_of_isLocalizationAway_of_isIdempotentElem
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (e : R)
    (he : IsIdempotentElem e) [IsLocalization.Away e S] :
    RingHom.Finite (algebraMap R S) :=
  RingHom.Finite.of_surjective (algebraMap R S)
    (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he)

/-- The specialization of step 1 to the canonical localization Localization.Away e. -/
theorem ringHomFinite_algebraMap_localizationAway_of_isIdempotentElem
    {R : Type u} [CommRing R] (e : R) (he : IsIdempotentElem e) :
    RingHom.Finite (algebraMap R (Localization.Away e)) :=
  ringHomFinite_algebraMap_of_isLocalizationAway_of_isIdempotentElem e he

/-! ### Step 2: D(e) for idempotent e is finite over Spec R -/

/-- For an idempotent e : R, D(e) is isomorphic to Spec R[e^{-1}] via
basicOpenIsoSpecAway e, and the map Spec R[e^{-1}] -> Spec R is finite because the
localization map is surjective. -/
theorem isFinite_opens_ι_basicOpen_of_isIdempotentElem
    {R : Type u} [CommRing R] (e : R) (he : IsIdempotentElem e) :
    IsFinite (Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen e)) := by
  haveI hfin : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away e)))) := by
    rw [IsFinite.SpecMap_iff]
    exact ringHomFinite_algebraMap_localizationAway_of_isIdempotentElem e he
  haveI : IsFinite ((basicOpenIsoSpecAway (R := CommRingCat.of R) e).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (CommRingCat.of R) (Localization.Away e)))) := inferInstance
  simpa [basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R) e] using this

/-! ### Step 3: clopen opens of an affine scheme are finite over the scheme -/

/-- A clopen open subscheme of the spectrum of a commutative ring is finite over it. -/
theorem isFinite_opens_ι_of_isClopen_spec
    {R : Type u} [CommRing R]
    (U : (Spec (CommRingCat.of R)).Opens)
    (hU : IsClopen (U : Set (Spec (CommRingCat.of R)))) :
    IsFinite U.ι := by
  obtain ⟨e, he, hUe⟩ := PrimeSpectrum.isClopen_iff.mp hU
  rw [show U = PrimeSpectrum.basicOpen e from TopologicalSpace.Opens.ext hUe]
  exact isFinite_opens_ι_basicOpen_of_isIdempotentElem e he

/-! ### Step 4: composing a clopen open subscheme with a finite morphism -/

/-- If f : X ⟶ S is finite and U ⊆ X is a clopen open subscheme, then
U.ι ≫ f : U ⟶ S is finite. -/
theorem isFinite_opens_ι_comp_of_isClopen
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (U : X.Opens) (hU : IsClopen (U : Set X)) :
    IsFinite (U.ι ≫ f) := by
  have hUc : IsClosed (Set.range U.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hU.isClosed
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι hUc
  infer_instance

end ClopenFinite

namespace FiniteGroupQuotient


open CategoryTheory
open CategoryTheory.Limits


section AffineInvariants

variable (R B G : Type u)
  [CommRing R] [CommRing B] [Algebra R B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The fixed-point subalgebra B^G of a commutative R-algebra B under the
action of a group G by R-algebra automorphisms. -/
noncomputable def fixedPointSubalgebra : Subalgebra R B :=
  FixedPoints.subalgebra R B G

/-- The inclusion of the fixed-point subalgebra B^G into B. -/
noncomputable def fixedPointInclusion : fixedPointSubalgebra R B G →ₐ[R] B :=
  (fixedPointSubalgebra R B G).val

/-- The inclusion B^G → B viewed as a ring homomorphism. -/
noncomputable def fixedPointInclusionRingHom :
    fixedPointSubalgebra R B G →+* B :=
  (fixedPointInclusion R B G).toRingHom

/-- The canonical affine quotient morphism Spec B ⟶ Spec (B^G). -/
noncomputable def affineQuotientMap :
    AlgebraicGeometry.Spec (CommRingCat.of B) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of (fixedPointSubalgebra R B G)) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (fixedPointInclusionRingHom R B G))

/-- Every group element fixes the image of the inclusion B^G → B pointwise. -/
theorem fixedPointInclusion_smul (g : G) (x : fixedPointSubalgebra R B G) :
    g • (fixedPointInclusion R B G x : B) = fixedPointInclusion R B G x := by
  exact x.2 g

/-- The inclusion B^G → B is a morphism of R-algebras, so its composite with
the structure map of B^G is the structure map of B. -/
theorem fixedPointInclusion_comp_algebraMap :
    (fixedPointInclusionRingHom R B G).comp
        (algebraMap R (fixedPointSubalgebra R B G)) =
      algebraMap R B := by
  ext r
  exact (fixedPointInclusion R B G).commutes r

/-- The ring automorphism of B induced by a group element g : G. -/
noncomputable def groupActionRingEquiv (g : G) : B ≃+* B :=
  MulSemiringAction.toRingEquiv G B g

/-- The scheme automorphism of Spec B induced by a group element g : G. -/
noncomputable def groupActionSpecAut (g : G) :
    AlgebraicGeometry.Spec (CommRingCat.of B) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of B) :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (groupActionRingEquiv B G g : B →+* B))

/-- The affine quotient morphism is invariant under the automorphism of Spec B
induced by every group element. -/
theorem groupActionSpecAut_comp_affineQuotientMap (g : G) :
    groupActionSpecAut B G g ≫ affineQuotientMap R B G = affineQuotientMap R B G := by
  unfold groupActionSpecAut affineQuotientMap
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  simpa [groupActionRingEquiv, fixedPointInclusionRingHom] using
    fixedPointInclusion_smul R B G g x

/-- The affine quotient morphism is a morphism of affine R-schemes: it is
compatible with the canonical structure morphisms to Spec R. -/
theorem affineQuotientMap_comp_specMap_algebraMap :
    affineQuotientMap R B G ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (fixedPointSubalgebra R B G))) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  unfold affineQuotientMap
  rw [← AlgebraicGeometry.Spec.map_comp]
  refine congrArg AlgebraicGeometry.Spec.map ?_
  rw [← CommRingCat.ofHom_comp]
  exact congrArg CommRingCat.ofHom (fixedPointInclusion_comp_algebraMap R B G)

end AffineInvariants

section ColimitInterface

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G]
variable (F : SingleObj G ⥤ C)
variable [HasCoproduct (fun _ : G => F.obj (SingleObj.star G))]

/-- The morphism out of the G-indexed coproduct of F.obj () whose g-th
component is the action map F.map g. -/
noncomputable abbrev actionCoproductMap :
    (∐ fun _ : G => F.obj (SingleObj.star G)) ⟶ F.obj (SingleObj.star G) :=
  Sigma.desc (fun g => F.map g)

/-- The morphism out of the G-indexed coproduct of F.obj () whose every
component is an identity. -/
noncomputable abbrev identityCoproductMap :
    (∐ fun _ : G => F.obj (SingleObj.star G)) ⟶ F.obj (SingleObj.star G) :=
  Sigma.desc (fun _ => 𝟙 (F.obj (SingleObj.star G)))

/-- The g-th inclusion followed by the action coproduct map is F.map g. -/
@[simp]
theorem sigmaIota_actionCoproductMap (g : G) :
    Sigma.ι (fun _ : G => F.obj (SingleObj.star G)) g ≫ actionCoproductMap F =
      F.map g := by
  change Sigma.ι (fun _ : G => F.obj (SingleObj.star G)) g ≫
      Sigma.desc (fun g => F.map g) = F.map g
  exact Sigma.ι_desc _ _

/-- The g-th inclusion followed by the identity coproduct map is the identity
of F.obj (). -/
@[simp]
theorem sigmaIota_identityCoproductMap (g : G) :
    Sigma.ι (fun _ : G => F.obj (SingleObj.star G)) g ≫
        identityCoproductMap F =
      𝟙 (F.obj (SingleObj.star G)) := by
  change Sigma.ι (fun _ : G => F.obj (SingleObj.star G)) g ≫
      Sigma.desc (fun _ => 𝟙 (F.obj (SingleObj.star G))) =
    𝟙 (F.obj (SingleObj.star G))
  exact Sigma.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The two canonical maps out of the G-indexed coproduct coequalize on every
cocone over F. -/
theorem cocone_condition (s : Cocone F) :
    actionCoproductMap F ≫ s.ι.app (SingleObj.star G) =
      identityCoproductMap F ≫ s.ι.app (SingleObj.star G) := by
  apply Sigma.hom_ext
  intro g
  rw [← Category.assoc, ← Category.assoc, sigmaIota_actionCoproductMap,
    sigmaIota_identityCoproductMap]
  have h := Cocone.w s (j := SingleObj.star G) (j' := SingleObj.star G) g
  rw [h, Category.id_comp]

variable [HasCoequalizer (actionCoproductMap F) (identityCoproductMap F)]

/-- The quotient of F.obj () by the action of G, defined as the coequalizer of
the action map and the identity map out of the G-indexed coproduct. -/
noncomputable abbrev quotientObject : C :=
  coequalizer (actionCoproductMap F) (identityCoproductMap F)

/-- The canonical projection from F.obj () to the quotient object. -/
noncomputable abbrev quotientMap : F.obj (SingleObj.star G) ⟶ quotientObject F :=
  coequalizer.π (actionCoproductMap F) (identityCoproductMap F)

/-- The action map F.map g followed by the quotient projection is the quotient
projection, for every g : G. -/
theorem action_comp_quotientMap (g : G) :
    F.map g ≫ quotientMap F = quotientMap F := by
  have h := congrArg
    (fun t => Sigma.ι (fun _ : G => F.obj (SingleObj.star G)) g ≫ t)
    (coequalizer.condition (actionCoproductMap F) (identityCoproductMap F))
  simpa only [quotientMap, quotientObject, ← Category.assoc,
    sigmaIota_actionCoproductMap, sigmaIota_identityCoproductMap,
    Category.id_comp] using h

/-- The cocone over F with point the coequalizer of the canonical pair and leg
the coequalizer projection. -/
noncomputable abbrev colimitCocone : Cocone F where
  pt := coequalizer (actionCoproductMap F) (identityCoproductMap F)
  ι := SingleObj.natTrans (F := F)
    (G := (Functor.const (SingleObj G)).obj
      (coequalizer (actionCoproductMap F) (identityCoproductMap F)))
    (coequalizer.π (actionCoproductMap F) (identityCoproductMap F))
    (by
      intro g
      erw [Functor.const_obj_map]
      show F.map g ≫ coequalizer.π (actionCoproductMap F) (identityCoproductMap F) =
        coequalizer.π (actionCoproductMap F) (identityCoproductMap F) ≫
          𝟙 (coequalizer (actionCoproductMap F) (identityCoproductMap F))
      rw [Category.comp_id]
      simpa only [quotientMap] using action_comp_quotientMap F g)

/-- The coequalizer cocone is a colimit cocone for F. -/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc s := coequalizer.desc (s.ι.app (SingleObj.star G)) (cocone_condition F s)
  fac s j := by
    have hj : j = SingleObj.star G := Subsingleton.elim j _
    subst hj
    change coequalizer.π (actionCoproductMap F) (identityCoproductMap F) ≫
        coequalizer.desc (s.ι.app (SingleObj.star G)) (cocone_condition F s) =
      s.ι.app (SingleObj.star G)
    exact coequalizer.π_desc _ _
  uniq s m hm := by
    apply coequalizer.hom_ext
    change (colimitCocone F).ι.app (SingleObj.star G) ≫ m =
      coequalizer.π (actionCoproductMap F) (identityCoproductMap F) ≫
        coequalizer.desc (s.ι.app (SingleObj.star G)) (cocone_condition F s)
    exact (hm (SingleObj.star G)).trans
      (coequalizer.π_desc (s.ι.app (SingleObj.star G)) (cocone_condition F s)).symm

/-- If the canonical pair of maps out of the G-indexed coproduct has a
coequalizer, then F has a colimit. -/
theorem hasColimit_of_hasCoequalizer : HasColimit F :=
  HasColimit.mk ⟨colimitCocone F, colimitCoconeIsColimit F⟩

omit [HasCoequalizer (actionCoproductMap F) (identityCoproductMap F)] in
/-- In particular, if C has colimits of shape WalkingParallelPair, the
coequalizer condition is automatic. -/
theorem hasColimit_of_hasColimitsOfShape_walkingParallelPair
    [HasColimitsOfShape WalkingParallelPair C] : HasColimit F := by
  haveI : HasCoequalizer (actionCoproductMap F) (identityCoproductMap F) :=
    inferInstance
  exact hasColimit_of_hasCoequalizer F

end ColimitInterface

section FiniteCoproductsVersion

variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [Fintype G]
variable (F : SingleObj G ⥤ C)
variable [HasFiniteCoproducts C] [HasColimitsOfShape WalkingParallelPair C]

/-- If G is finite and C has finite coproducts and coequalizers, then every
functor out of SingleObj G has a colimit. -/
theorem hasColimit_of_finiteCoproducts_and_coequalizers : HasColimit F := by
  haveI : HasCoproduct (fun _ : G => F.obj (SingleObj.star G)) := inferInstance
  haveI : HasCoequalizer (actionCoproductMap F) (identityCoproductMap F) :=
    inferInstance
  exact hasColimit_of_hasColimitsOfShape_walkingParallelPair F

end FiniteCoproductsVersion

end FiniteGroupQuotient

end ClopenFiniteComplement
end LeanFormal.IUT.Foundations.Geometry