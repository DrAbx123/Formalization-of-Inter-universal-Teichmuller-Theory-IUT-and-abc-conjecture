import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientDesc
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationActionColimit
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFixedPointDescNormalForm
import Mathlib.Tactic

/-!
# Uniqueness layer for the regular permutation cocone (scratch)

Given an explicit desc family for cocones of
regularPermutationActionFunctor R G, this file records the cover-extensionality
step and the exact fac/uniq data needed to package the production cocone as an
IsColimit.  It does not construct desc; that is the affine-universal-property
part owned by qside.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open AffineLocalQuotientGluingConstruct
open ABCBridge.RegularPermutationQuotientDesc
open RegularPermutationActionColimit
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.AffineFixedPointDescNormalForm
open ABCBridge.RegularPermutationSectionsInvariance

noncomputable section

namespace RegularPermutationCoconeUniqueness

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

abbrev actionFunctor (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  regularPermutationActionFunctor R G

abbrev sourceCover (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  regularPermutationCover R G

abbrev quotientCover (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  regularPermutationQuotientCover R G

/-- Cover morphisms over Spec R are determined by their underlying scheme
morphisms. -/
theorem finiteEtaleCoverHom_ext {X Y : FiniteEtaleCover (Spec (CommRingCat.of R))}
    {f g : X ⟶ Y}
    (h : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left =
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map g).left) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact h

/-- The component of the production cocone at the unique object is the chart map. -/
theorem regularPermutationCocone_ι_star :
    (regularPermutationCocone R G).ι.app (SingleObj.star G) =
      regularPermutationChartMap R G := rfl

/-- The component at every object is the chart map. -/
theorem regularPermutationCocone_ι_eq_chart (j : SingleObj G) :
    (regularPermutationCocone R G).ι.app j = regularPermutationChartMap R G := by
  have hj : j = SingleObj.star G := Subsingleton.elim _ _
  rw [hj, regularPermutationCocone_ι_star]

/-- Fac data for a candidate desc family. -/
def HasDescFac
    (desc : ∀ c : Cocone (actionFunctor R G),
      quotientCover R G ⟶ c.pt) : Prop :=
  ∀ c, regularPermutationChartMap R G ≫ desc c =
    c.ι.app (SingleObj.star G)

/-- Uniqueness data for a candidate desc family. -/
def HasDescUniq
    (desc : ∀ c : Cocone (actionFunctor R G),
      quotientCover R G ⟶ c.pt) : Prop :=
  ∀ (c : Cocone (actionFunctor R G)) (m : quotientCover R G ⟶ c.pt),
    regularPermutationChartMap R G ≫ m = c.ι.app (SingleObj.star G) →
      m = desc c

/-- Fac and uniqueness data together give the actual IsColimit of the production
regular permutation cocone.  This is the categorical packaging; the affine
universal property must supply desc and these two hypotheses. -/
noncomputable def isColimitOfDesc
    (desc : ∀ c : Cocone (actionFunctor R G),
      quotientCover R G ⟶ c.pt)
    (hfac : HasDescFac (R := R) (G := G) desc)
    (huniq : HasDescUniq (R := R) (G := G) desc) :
    IsColimit (regularPermutationCocone R G) := by
  refine IsColimit.mk (fun c => desc c) ?_ ?_
  · intro c j
    rw [regularPermutationCocone_ι_eq_chart (R := R) (G := G) j]
    exact hfac c
  · intro c m hm
    exact huniq c m (by
      rw [← regularPermutationCocone_ι_eq_chart (R := R) (G := G) (SingleObj.star G)]
      exact hm (SingleObj.star G))


/-- The production desc family satisfies the fac equation. -/
lemma desc_hasFac (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    HasDescFac (R := R) (G := G)
      (fun c => desc (R := R) (G := G) c) := by
  intro c
  -- unfold desc and finiteEtaleCoverHomMk
  change regularPermutationChartMap R G ≫
      finiteEtaleCoverHomMk (descF (R := R) (G := G) c)
        (descW (R := R) (G := G) c) = c.ι.app (SingleObj.star G)
  apply finiteEtaleCoverHom_ext (R := R)
  let f : regularPermutationCover R G ⟶ c.pt := by
    change (regularPermutationActionFunctor R G).obj (SingleObj.star G) ⟶ c.pt
    exact c.ι.app (SingleObj.star G)
  change (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
      (regularPermutationChartMap R G ≫ finiteEtaleCoverHomMk (descF (R := R) (G := G) c)
        (descW (R := R) (G := G) c))).left =
    (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left
  change (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
      (regularPermutationChartMap R G)).left ≫
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
        (finiteEtaleCoverHomMk (descF (R := R) (G := G) c)
          (descW (R := R) (G := G) c))).left =
    (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left
  have hchart : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
        (regularPermutationChartMap R G)).left =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) := rfl
  have hdesc : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
        (finiteEtaleCoverHomMk (descF (R := R) (G := G) c)
          (descW (R := R) (G := G) c))).left = descF (R := R) (G := G) c := rfl
  rw [hchart, hdesc]
  change Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) ≫
      descF (R := R) (G := G) c =
    (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left
  rw [descF]
  change Spec.map (CommRingCat.ofHom
        (fixedPointInclusion R (G → R) G : _ →+* (G → R))) ≫
      (Spec.map (CommRingCat.ofHom (descPsi0 (R := R) (G := G) c).toRingHom) ≫
        c.pt.carrier.isoSpec.inv) = _
  rw [← Category.assoc]
  rw [← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]
  erw [show (fixedPointInclusion R (G → R) G).toRingHom.comp
        (descPsi0 (R := R) (G := G) c).toRingHom =
          (descPhi (R := R) (G := G) c).toRingHom from
      congrArg AlgHom.toRingHom (descPsi0_spec (R := R) (G := G) c)]
  -- now Spec.map descPhi followed by isoSpec.inv, and sectionsAlgMap_spec
  rw [show Spec.map (CommRingCat.ofHom (descPhi (R := R) (G := G) c).toRingHom) =
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫
        c.pt.carrier.isoSpec.hom from by
    have hspec := ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap_spec
      (R := R) (G := G) c
    change Spec.map (CommRingCat.ofHom (sectionsAlgMap R G c)) =
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left ≫
        c.pt.carrier.isoSpec.hom
    rw [show (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left =
        (c.ι.app (SingleObj.star G)).hom.left from rfl]
    exact hspec]
  erw [Category.assoc, c.pt.carrier.isoSpec.hom_inv_id, Category.comp_id]


/-- The production desc family satisfies the uniqueness equation. -/
lemma desc_hasUniq (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G] :
    HasDescUniq (R := R) (G := G)
      (fun c => desc (R := R) (G := G) c) := by
  intro c m hm
  let f : regularPermutationCover R G ⟶ c.pt := by
    change (regularPermutationActionFunctor R G).obj (SingleObj.star G) ⟶ c.pt
    exact c.ι.app (SingleObj.star G)
  let mOver := (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map m
  have hm_eq : regularPermutationChartMap R G ≫ m = f := hm
  have hmleft : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
      (regularPermutationChartMap R G ≫ m)).left =
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left :=
    congrArg (fun g => (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map g).left)
      hm_eq
  have hmcomp : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
        (regularPermutationChartMap R G)).left ≫ mOver.left =
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left := by
    simpa [mOver, Functor.map_comp] using hmleft
  let ψr : Γ(c.pt.carrier, ⊤) →+* fixedPointSubalgebra R (G → R) G :=
    (Spec.preimage (mOver.left ≫ c.pt.carrier.isoSpec.hom)).hom
  have hψr_spec : Spec.map (CommRingCat.ofHom ψr) =
      mOver.left ≫ c.pt.carrier.isoSpec.hom :=
    Spec.map_preimage _
  have hchart : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
        (regularPermutationChartMap R G)).left =
      Spec.map (CommRingCat.ofHom
        (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))) := rfl
  have hcomp : Spec.map (CommRingCat.ofHom
        ((Subalgebra.val (FixedPoints.subalgebra R (G → R) G)).toRingHom.comp ψr)) =
      Spec.map (CommRingCat.ofHom (descPhi (R := R) (G := G) c).toRingHom) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    erw [hψr_spec]
    erw [← hchart]
    erw [← Category.assoc, hmcomp]
    have hspec := ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap_spec
      (R := R) (G := G) c
    rw [show (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left =
        (c.ι.app (SingleObj.star G)).hom.left from rfl]
    rw [show (descPhi (R := R) (G := G) c).toRingHom =
        ABCBridge.RegularPermutationSectionsInvariance.sectionsAlgMap R G c from rfl]
    exact hspec.symm
  have hcomp_ring : (Subalgebra.val (FixedPoints.subalgebra R (G → R) G)).toRingHom.comp ψr =
      (descPhi (R := R) (G := G) c).toRingHom :=
    CommRingCat.hom_ext_iff.mp (Spec.map_injective hcomp)
  let ψ : Γ(c.pt.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R (G → R) G :=
    { toRingHom := ψr
      commutes' := by
        intro r
        apply Subtype.val_injective
        have hval := congrArg (fun g => g (algebraMap R Γ(c.pt.carrier, ⊤) r)) hcomp_ring
        change (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))
            (ψr (algebraMap R Γ(c.pt.carrier, ⊤) r)) =
          (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))
            (algebraMap R (fixedPointSubalgebra R (G → R) G) r)
        calc
          (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))
              (ψr (algebraMap R Γ(c.pt.carrier, ⊤) r))
              = (descPhi (R := R) (G := G) c)
                  (algebraMap R Γ(c.pt.carrier, ⊤) r) := hval
          _ = algebraMap R (G → R) r := (descPhi (R := R) (G := G) c).commutes r
          _ = (Subalgebra.val (FixedPoints.subalgebra R (G → R) G))
                (algebraMap R (fixedPointSubalgebra R (G → R) G) r) := rfl }
  have hψ : (fixedPointInclusion R (G → R) G).comp ψ = descPhi (R := R) (G := G) c := by
    apply AlgHom.ext
    intro b
    exact congrArg (fun g => g b) hcomp_ring
  have hψeq : ψ = descPsi0 (R := R) (G := G) c :=
    descPsi0_unique (R := R) (G := G) c ψ hψ
  have hscheme : mOver.left ≫ c.pt.carrier.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (descPsi0 (R := R) (G := G) c).toRingHom) := by
    rw [← hψr_spec]
    change Spec.map (CommRingCat.ofHom ψ.toRingHom) =
      Spec.map (CommRingCat.ofHom (descPsi0 (R := R) (G := G) c).toRingHom)
    rw [hψeq]
  have hmleft_eq : mOver.left = descF (R := R) (G := G) c := by
    have h := congrArg (fun u => u ≫ c.pt.carrier.isoSpec.inv) hscheme
    erw [Category.assoc, c.pt.carrier.isoSpec.hom_inv_id, Category.comp_id] at h
    rw [descF, ABCBridge.AffineFixedPointDescNormalForm.descSchemeMap]
    exact h
  apply finiteEtaleCoverHom_ext (R := R)
  change mOver.left = (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
    (finiteEtaleCoverHomMk (descF (R := R) (G := G) c)
      (descW (R := R) (G := G) c))).left
  change mOver.left = descF (R := R) (G := G) c
  exact hmleft_eq


/-- The production regular permutation cocone is the actual colimit. -/
noncomputable def regularPermutationCocone_isColimit (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Fintype G] :
    IsColimit (regularPermutationCocone R G) :=
  isColimitOfDesc (R := R) (G := G)
    (fun c => ABCBridge.RegularPermutationQuotientDesc.desc (R := R) (G := G) c)
    (desc_hasFac R G) (desc_hasUniq R G)

end RegularPermutationCoconeUniqueness
