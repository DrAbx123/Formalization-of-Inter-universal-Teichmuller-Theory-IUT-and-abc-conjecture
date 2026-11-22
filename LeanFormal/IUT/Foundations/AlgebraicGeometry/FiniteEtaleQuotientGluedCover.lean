import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingFree
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsGeneralAssembly
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.Connected

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

/-!
# Glued quotient covers and their scheme-level universal property

New production file (primespine ownership, L0.3).  It promotes the packaging of
an affine-local quotient preglue datum into a finite etale cover, and proves the
scheme-level universal property of the glued scheme.

The free/trivialized preglue data and cover are supplied by the production module
AffineLocalQuotientGluingFree (freeTorsorPreglueData, freeTorsorFiniteEtaleCover,
freeTorsorGluedIso).  The scheme-level universal property proved here is the
descent half needed for the free/trivialized quotient cocone; the remaining
SingleObj G cocone/IsColimit packaging is recorded as an explicit residual (no
provider general claim, no colimit instance, no card).
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct

universe u

open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

/-- Package the glued quotient map as a finite etale cover of S.  Finiteness is
an explicit argument; etaleness is the production gluedMapOfCompatible_etale. -/
noncomputable def AffineLocalQuotientPreglueData.toFiniteEtaleCoverOfIsFinite
    (P : AffineLocalQuotientPreglueData S)
    (hq : ∀ i j, pullback.fst ((P.toSchemeGlueData).ι i)
        ((P.toSchemeGlueData).ι j) ≫ P.q i =
        pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ P.q j)
    (hfin : IsFinite (P.gluedMapOfCompatible hq)) :
    FiniteEtaleCover S :=
  FiniteEtaleCover.mk (P.gluedMapOfCompatible hq)
    (P.gluedMapOfCompatible_etale hq) hfin

/-- Scheme-level universal property of the glued quotient: compatible morphisms
from the affine quotient charts to a scheme Z glue to a morphism out of the glued
scheme. -/
noncomputable def AffineLocalQuotientPreglueData.descOfCompatible
    (P : AffineLocalQuotientPreglueData S) (Z : Scheme.{u})
    (f : ∀ i : P.J, P.U i ⟶ Z)
    (hf : ∀ i j : P.J,
      pullback.fst ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ f j) :
    (P.toSchemeGlueData).glued ⟶ Z :=
  (P.toSchemeGlueData).openCover.glueMorphisms f hf

/-- Restriction of the glued morphism to each affine quotient chart. -/
theorem AffineLocalQuotientPreglueData.descOfCompatible_ι
    (P : AffineLocalQuotientPreglueData S) (Z : Scheme.{u})
    (f : ∀ i : P.J, P.U i ⟶ Z)
    (hf : ∀ i j : P.J,
      pullback.fst ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ f j)
    (i : P.J) :
    (P.toSchemeGlueData).ι i ≫ P.descOfCompatible Z f hf = f i :=
  (P.toSchemeGlueData).openCover.ι_glueMorphisms f hf i

/-- Uniqueness in the scheme-level universal property of the glued quotient. -/
theorem AffineLocalQuotientPreglueData.descOfCompatible_unique
    (P : AffineLocalQuotientPreglueData S) (Z : Scheme.{u})
    (f : ∀ i : P.J, P.U i ⟶ Z)
    (hf : ∀ i j : P.J,
      pullback.fst ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ f i =
      pullback.snd ((P.toSchemeGlueData).ι i) ((P.toSchemeGlueData).ι j) ≫ f j)
    (u : (P.toSchemeGlueData).glued ⟶ Z)
    (hu : ∀ i : P.J, (P.toSchemeGlueData).ι i ≫ u = f i) :
    u = P.descOfCompatible Z f hf := by
  refine (P.toSchemeGlueData).openCover.hom_ext u (P.descOfCompatible Z f hf) (fun i => ?_)
  change (P.toSchemeGlueData).ι i ≫ u =
    (P.toSchemeGlueData).ι i ≫ P.descOfCompatible Z f hf
  rw [hu i, P.descOfCompatible_ι Z f hf i]

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct



/-! ## The fully trivialized (constant) action colimit

This is the first fully trivialized case of the free/trivialized quotient: the
action diagram is the constant functor with value X.  Mathlib's connected-index
constant-cocone API (constCocone / isColimitConstCocone) constructs the actual
colimit without any definitional-equality casts. -/

namespace AffineLocalQuotientGluingConstruct

/-- The actual colimit cocone of the constant SingleObj G diagram at X. -/
noncomputable def trivializedActionCocone {G : Type u} [Group G]
    {S : Scheme.{u}} (X : FiniteEtaleCover S) :
    Cocone ((Functor.const (SingleObj G)).obj X) :=
  constCocone (SingleObj G) X

/-- The constant/trivialized action diagram has the actual colimit X. -/
noncomputable def isColimit_trivializedActionCocone {G : Type u} [Group G]
    {S : Scheme.{u}} (X : FiniteEtaleCover S) :
    IsColimit (trivializedActionCocone (G := G) X) :=
  isColimitConstCocone (SingleObj G) X

/-- The actual HasColimit of the constant SingleObj G diagram at X. -/
noncomputable abbrev hasColimit_trivializedAction {G : Type u} [Group G]
    {S : Scheme.{u}} (X : FiniteEtaleCover S) :
    HasColimit ((Functor.const (SingleObj G)).obj X) :=
  hasColimit_const_of_isConnected (SingleObj G) X

end AffineLocalQuotientGluingConstruct


/-! ## Affine target reduction

A finite etale cover over an affine base is affine (its structure map is finite,
hence affine), and the affine fixed-point universal property applies to the
coordinate algebra of any affine target. -/

section AffineTarget

universe v

variable (R A B G : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Group G] [MulSemiringAction G A]
  [SMulCommClass G R A]

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

/-- Any finite etale cover over the affine base Spec R is affine (its structure
map is finite, hence affine). -/
instance finiteEtaleCoverCarrier_isAffine
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) : IsAffine X.carrier := by
  haveI : IsFinite (FiniteEtaleCover.structureMap X) :=
    FiniteEtaleCover.finite_structureMap X
  exact isAffine_of_isAffineHom (FiniteEtaleCover.structureMap X)

/-- Affine-target reduction: an invariant R-algebra map B -> A induces a unique
(in the algebra category) map on affine quotient charts.  This is the Spec-level
form of qside's affineFixedPointQuotient_universal, used to build the desc map for
affine targets. -/
theorem affineFixedPointQuotient_universal_spec
    (φ : B →ₐ[R] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃ ψ : Spec (CommRingCat.of (fixedPointSubalgebra R A G)) ⟶
        Spec (CommRingCat.of B),
      Spec.map (CommRingCat.ofHom (fixedPointInclusion R A G : _ →+* A)) ≫ ψ =
        Spec.map (CommRingCat.ofHom (φ : B →+* A)) := by
  obtain ⟨ψ, hψ, -⟩ :=
    ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal R A G φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom (ψ : B →+* fixedPointSubalgebra R A G)), ?_⟩
  rw [← Spec.map_comp]
  have hcomp : (CommRingCat.ofHom (ψ : B →+* fixedPointSubalgebra R A G)) ≫
      (CommRingCat.ofHom (fixedPointInclusion R A G : _ →+* A)) =
        CommRingCat.ofHom (φ : B →+* A) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    ext b
    exact congrArg (fun f : B →ₐ[R] A => f b) hψ
  rw [hcomp]

end AffineTarget


/-- The R-algebra structure on the sections of a finite etale cover over the
affine base Spec R, induced by the structure morphism and the canonical
identification Γ(Spec R) ≅ R. -/
noncomputable def finiteEtaleCoverSectionsAlgebraMap
    (R : Type u) [CommRing R] (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    R →+* Γ(Z.carrier, ⊤) :=
  (FiniteEtaleCover.structureMap Z).appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom

/-- The corresponding Algebra R (Γ(Z)) instance, supplied locally where needed. -/
noncomputable instance finiteEtaleCoverSectionsAlgebra
    (R : Type u) [CommRing R] (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    Algebra R Γ(Z.carrier, ⊤) :=
  RingHom.toAlgebra (finiteEtaleCoverSectionsAlgebraMap R Z)


/-- Cover-morphism to coordinate-algebra conversion: for a cover morphism
f : X ⟶ Z over Spec R and an identification of X with Spec A, the composite
with the affine iso Z ≅ Spec Γ(Z) and Spec.preimage yields the corresponding
R-algebra map Γ(Z) → A. -/
noncomputable def coverMorphismToSectionsAlgHom
    (R : Type u) [CommRing R] {A : Type u} [CommRing A]
    {X Z : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (e : X.carrier ≅ Spec (CommRingCat.of A)) (f : X ⟶ Z) :
    Γ(Z.carrier, ⊤) →+* A :=
  (Spec.preimage (e.inv ≫ (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫ (Z.carrier).isoSpec.hom)).hom

/-- The conversion is the unique algebra map whose Spec map is the composite
with the affine isomorphism. -/
theorem specMap_coverMorphismToSectionsAlgHom
    (R : Type u) [CommRing R] {A : Type u} [CommRing A]
    {X Z : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (e : X.carrier ≅ Spec (CommRingCat.of A)) (f : X ⟶ Z) :
    Spec.map (CommRingCat.ofHom (coverMorphismToSectionsAlgHom R e f)) =
      e.inv ≫ (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫ (Z.carrier).isoSpec.hom := by
  apply Spec.map_preimage


/-! ## Regular permutation cover and fixed-point quotient chart -/

namespace AffineLocalQuotientGluingConstruct

/-- The regular permutation (trivialized free-torsor) cover Spec (G -> R) over
Spec R. -/
noncomputable def regularPermutationCover (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  FiniteEtaleCover.mk
    (Spec.map (CommRingCat.ofHom (algebraMap R (G → R))))
    (by
      apply HasRingHomProperty.Spec_iff.mpr
      exact RingHom.etale_algebraMap.mpr
        (inferInstance : Algebra.Etale R (G → R)))
    (by
      rw [AlgebraicGeometry.IsFinite.SpecMap_iff]
      change (algebraMap R (G → R)).Finite
      rw [RingHom.finite_algebraMap]
      exact inferInstance)

/-- The regular permutation fixed-point quotient chart Spec ((G -> R)^G) over
Spec R (kummer's regular fixed-point chart). -/
noncomputable def regularPermutationQuotientCover (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  FiniteEtaleCover.mk
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (FixedPoints.subalgebra R (G → R) G))))
    (by
      apply HasRingHomProperty.Spec_iff.mpr
      exact RingHom.etale_algebraMap.mpr
        (PermutationTorsorQuotient.regular_fixedPoints_etale (R := R) (G := G)))
    (by
      rw [AlgebraicGeometry.IsFinite.SpecMap_iff]
      change (algebraMap R (FixedPoints.subalgebra R (G → R) G)).Finite
      rw [RingHom.finite_algebraMap]
      exact PermutationTorsorQuotient.regular_fixedPoints_moduleFinite
        (R := R) (G := G))

end AffineLocalQuotientGluingConstruct


/-! ## Cover-level morphism constructor -/

namespace AffineLocalQuotientGluingConstruct

/-- Cover-level morphism constructor: a scheme morphism between the carriers
satisfying the over-S condition gives a morphism of finite etale covers.  This
avoids relying on definitional equality between full-subcategory homs and Over
homs. -/
noncomputable def finiteEtaleCoverHomMk {S : Scheme.{u}} {X Y : FiniteEtaleCover S}
    (f : X.carrier ⟶ Y.carrier)
    (w : f ≫ FiniteEtaleCover.structureMap Y = FiniteEtaleCover.structureMap X) :
    X ⟶ Y :=
  ObjectProperty.homMk
    (Over.homMk f (by
      simpa [FiniteEtaleCover.carrier, FiniteEtaleCover.structureMap] using w))

end AffineLocalQuotientGluingConstruct

namespace AffineLocalQuotientGluingConstruct

end AffineLocalQuotientGluingConstruct

namespace AffineLocalQuotientGluingConstruct

/-- The regular permutation chart map from the trivialized cover Spec (G -> R)
to its fixed-point quotient chart Spec ((G -> R)^G). -/
noncomputable def regularPermutationChartMap (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    regularPermutationCover R G ⟶ regularPermutationQuotientCover R G := by
  refine finiteEtaleCoverHomMk (X := regularPermutationCover R G)
    (Y := regularPermutationQuotientCover R G) ?_ ?_
  · change Spec (CommRingCat.of (G → R)) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R (G → R) G))
    exact Spec.map (CommRingCat.ofHom
      (Subalgebra.val (FixedPoints.subalgebra R (G → R) G)))
  · change Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra R (G → R) G))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (G → R)))
    rw [← Spec.map_comp]
    congr 1

end AffineLocalQuotientGluingConstruct

namespace AffineLocalQuotientGluingConstruct

/-- The G-action endomorphism of the regular permutation cover, induced by the
permutation action on (G -> R). -/
noncomputable def regularPermutationActionEnd (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] (g : G) :
    regularPermutationCover R G ⟶ regularPermutationCover R G := by
  refine finiteEtaleCoverHomMk (X := regularPermutationCover R G)
    (Y := regularPermutationCover R G) ?_ ?_
  · change Spec (CommRingCat.of (G → R)) ⟶ Spec (CommRingCat.of (G → R))
    exact Spec.map (CommRingCat.ofHom
      ((MulSemiringAction.toAlgEquiv R (G → R) g).toRingEquiv))
  · change Spec.map (CommRingCat.ofHom
        ((MulSemiringAction.toAlgEquiv R (G → R) g).toRingEquiv)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (G → R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (G → R)))
    rw [← Spec.map_comp]
    congr 1

end AffineLocalQuotientGluingConstruct

namespace AffineLocalQuotientGluingConstruct

open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-- Congruence for cover morphisms built by finiteEtaleCoverHomMk. -/
lemma finiteEtaleCoverHomMk_congr {S : Scheme.{u}} {X Y : FiniteEtaleCover S}
    {f g : X.carrier ⟶ Y.carrier} (h : f = g)
    {wf : f ≫ FiniteEtaleCover.structureMap Y = FiniteEtaleCover.structureMap X}
    {wg : g ≫ FiniteEtaleCover.structureMap Y = FiniteEtaleCover.structureMap X} :
    finiteEtaleCoverHomMk f wf = finiteEtaleCoverHomMk g wg := by
  subst h
  congr 1

end AffineLocalQuotientGluingConstruct

namespace AffineLocalQuotientGluingConstruct

/-- The action endomorphism at the identity is the identity cover morphism. -/
lemma regularPermutationActionEnd_one (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    regularPermutationActionEnd R G (1 : G) =
      𝟙 (regularPermutationCover R G) := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  change Spec.map (CommRingCat.ofHom
      ((MulSemiringAction.toAlgEquiv R (G → R) (1 : G)).toRingEquiv.toRingHom)) = 𝟙 _
  rw [← Spec.map_id (CommRingCat.of (G → R))]
  exact congrArg Spec.map (by
    ext r
    simp)

/-- The action endomorphisms are covariant for multiplication. -/
lemma regularPermutationActionEnd_mul (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] (a b : G) :
    regularPermutationActionEnd R G (a * b) =
      regularPermutationActionEnd R G a ≫
        regularPermutationActionEnd R G b := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  change Spec.map (CommRingCat.ofHom
        ((MulSemiringAction.toAlgEquiv R (G → R) (a * b)).toRingEquiv.toRingHom)) =
      Spec.map (CommRingCat.ofHom
          ((MulSemiringAction.toAlgEquiv R (G → R) a).toRingEquiv.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          ((MulSemiringAction.toAlgEquiv R (G → R) b).toRingEquiv.toRingHom))
  rw [← Spec.map_comp]
  exact congrArg Spec.map (by
    ext r
    simp [mul_smul])

end AffineLocalQuotientGluingConstruct

namespace AffineLocalQuotientGluingConstruct

/-- The regular permutation action functor SingleObj G to finite etale covers
over Spec R.  The inverse is used so that the contravariant Spec action becomes
covariant. -/
noncomputable def regularPermutationActionFunctor (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)) where
  obj _ := regularPermutationCover R G
  map f := regularPermutationActionEnd R G f⁻¹
  map_id x := by
    rw [SingleObj.id_as_one, inv_one]
    exact regularPermutationActionEnd_one R G
  map_comp f g := by
    rw [SingleObj.comp_as_mul, mul_inv_rev]
    exact regularPermutationActionEnd_mul R G f⁻¹ g⁻¹


/-- The regular chart map is invariant under every coordinate action
endomorphism. -/
lemma regularPermutationActionEnd_chartMap (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] (h : G) :
    regularPermutationActionEnd R G h ≫ regularPermutationChartMap R G =
      regularPermutationChartMap R G := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  change Spec.map (CommRingCat.ofHom
      ((MulSemiringAction.toAlgEquiv R (G → R) h).toRingEquiv.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom
        ((Subalgebra.val (FixedPoints.subalgebra R (G → R) G)).toRingHom)) =
    Spec.map (CommRingCat.ofHom
      (Subalgebra.val (FixedPoints.subalgebra R (G → R) G)).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg Spec.map (by
    ext x i
    change (MulSemiringAction.toAlgEquiv R (G → R) h) x.val i = x.val i
    rw [MulSemiringAction.toAlgEquiv_apply]
    exact congrFun (x.2 h) i)

/-- The regular permutation quotient cocone with point the fixed-point chart
cover and the chart map as projection. -/
noncomputable def regularPermutationCocone (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    Cocone (regularPermutationActionFunctor R G) :=
  Cocone.mk (regularPermutationQuotientCover R G)
    (SingleObj.natTrans (regularPermutationChartMap R G) (by
      intro a
      change regularPermutationActionEnd R G a⁻¹ ≫
          regularPermutationChartMap R G =
        regularPermutationChartMap R G ≫ 𝟙 _
      rw [Category.comp_id]
      exact regularPermutationActionEnd_chartMap R G a⁻¹))

end AffineLocalQuotientGluingConstruct

/-! ## Exact residual for the free/trivialized SingleObj G colimit

The scheme-level universal property above is the descent half, and the free
preglue data/cover is production (AffineLocalQuotientGluingFree).  To finish the
free/trivialized SingleObj G to FiniteEtaleCover (Spec R) cocone/IsColimit one
still needs:

1. the explicit permutation/free action functor on the trivialized cover and the
   identification of its cocone target with the free quotient cover;
2. G-invariance of the chart quotient maps q i, so the glued map factors through
   the quotient action;
3. conversion of an arbitrary finite etale cover target Z over the affine base to
   its coordinate algebra (Z is affine because its structure map is finite) and
   application of qside's affineFixedPointQuotient_universal to build desc;
4. cocone naturality/uniqueness and the IsColimit packaging for the action
   diagram.

No general provider or colimit instance is claimed here; no card.
-/
