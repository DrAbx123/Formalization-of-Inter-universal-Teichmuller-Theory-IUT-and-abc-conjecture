import LeanFormal.IUT.Foundations.AlgebraicGeometry.IsospecSectionsCoherence
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientActionDataFromCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientUniversalProperty
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open ABCBridge.IsospecSectionsCoherence
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.CoverSectionsAction
open ABCBridge.AffineQuotientActionDataFromCover
open LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientActionCocone

noncomputable section
namespace ABCBridge.AffineBaseFiniteEtaleQuotients
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

/-- Sections of an affine finite-etale cover are finite etale over R. -/
theorem finiteEtaleCoverSections_etale
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    Algebra.Etale R Γ(Z.carrier, ⊤) := by
  apply RingHom.etale_algebraMap.mp
  change (CommRingCat.ofHom (algebraMap R Γ(Z.carrier, ⊤))).hom.Etale
  rw [← HasRingHomProperty.Spec_iff (P := @Etale)]
  have h : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z.carrier, ⊤))) =
      Z.carrier.isoSpec.inv ≫ Z.structureMap := by
    have hs := isoSpec_sectionsAlgebraMap (R := R) Z
    simpa [Iso.inv_hom_id_assoc] using
      congrArg (fun f => Z.carrier.isoSpec.inv ≫ f) hs
  rw [h]
  haveI : Etale Z.structureMap := Z.etale_structureMap
  exact MorphismProperty.comp_mem (@Etale) Z.carrier.isoSpec.inv Z.structureMap
    inferInstance inferInstance

theorem finiteEtaleCoverSections_finite
    (Z : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    Module.Finite R Γ(Z.carrier, ⊤) := by
  change (CommRingCat.ofHom (algebraMap R Γ(Z.carrier, ⊤))).hom.Finite
  rw [← AlgebraicGeometry.IsFinite.SpecMap_iff]
  have h : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z.carrier, ⊤))) =
      Z.carrier.isoSpec.inv ≫ Z.structureMap := by
    have hs := isoSpec_sectionsAlgebraMap (R := R) Z
    simpa [Iso.inv_hom_id_assoc] using
      congrArg (fun f => Z.carrier.isoSpec.inv ≫ f) hs
  rw [h]
  haveI : IsFinite Z.structureMap := Z.finite_structureMap
  exact MorphismProperty.comp_mem (@IsFinite) Z.carrier.isoSpec.inv Z.structureMap
    inferInstance inferInstance


/-- The action of G on the object of a single-object diagram, induced by
functoriality from the group isomorphisms of the single object. -/
noncomputable def actionOfDiagram
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) :
    G →* CategoryTheory.Aut (F.obj (SingleObj.star G)) :=
  (F.mapAut (SingleObj.star G)).comp
    ((Units.toAut G).toMonoidHom.comp (toUnits (G := G)).toMonoidHom)



/-- The scheme automorphism induced by the diagram action is the underlying
scheme map of the diagram automorphism. -/
theorem coverAutSchemeIso_action_hom
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) (g : G) :
    (coverAutSchemeIso (F.obj (SingleObj.star G)) (actionOfDiagram F) g).hom =
      (F.map g).hom.left := by
  change (F.map ((Units.toAut G (toUnits (G := G) g)).hom)).hom.left =
    (F.map g).hom.left
  rw [Units.toAut_hom, SingleObj.toEnd_def]
  rfl

/-- The section map of a diagram action morphism is the induced ring
automorphism. -/
theorem coverSectionsAlgHom_map_eq
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) (g : G) :
    ((ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom
        (R := R) (X := F.obj (SingleObj.star G))
        (Z := F.obj (SingleObj.star G)) (F.map g)) :
      Γ((F.obj (SingleObj.star G)).carrier, ⊤) →+*
        Γ((F.obj (SingleObj.star G)).carrier, ⊤)) =
      (coverSectionsRingEquiv (F.obj (SingleObj.star G)) (actionOfDiagram F) g :
        Γ((F.obj (SingleObj.star G)).carrier, ⊤) →+*
          Γ((F.obj (SingleObj.star G)).carrier, ⊤)) := by
  let Z := F.obj (SingleObj.star G)
  have h : CommRingCat.ofHom
      (ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom
        (R := R) (X := Z) (Z := Z) (F.map g) :
        Γ(Z.carrier, ⊤) →+* Γ(Z.carrier, ⊤)) =
      CommRingCat.ofHom
        (coverSectionsRingEquiv Z (actionOfDiagram F) g :
          Γ(Z.carrier, ⊤) →+* Γ(Z.carrier, ⊤)) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (coverMorphismToSectionsAlgHom R
      Z.carrier.isoSpec (F.map g))) = _
    rw [specMap_coverMorphismToSectionsAlgHom]
    have hnat := coverSectionsSpecAut_agrees Z (actionOfDiagram F) g
    have hact : (coverAutSchemeIso Z (actionOfDiagram F) g).hom = (F.map g).hom.left :=
      coverAutSchemeIso_action_hom (R := R) F g
    have hspec : Spec.map (CommRingCat.ofHom (coverSectionsRingEquiv Z (actionOfDiagram F) g :
        Γ(Z.carrier, ⊤) →+* Γ(Z.carrier, ⊤))) =
        (coverSectionsSpecAut Z (actionOfDiagram F) g).hom := rfl
    rw [hspec]
    symm
    calc
      (coverSectionsSpecAut Z (actionOfDiagram F) g).hom
          = Z.carrier.isoSpec.inv ≫
              (Z.carrier.isoSpec.hom ≫
                (coverSectionsSpecAut Z (actionOfDiagram F) g).hom) := by
            rw [Iso.inv_hom_id_assoc]
      _ = Z.carrier.isoSpec.inv ≫
            ((coverAutSchemeIso Z (actionOfDiagram F) g).hom ≫
              Z.carrier.isoSpec.hom) := by
            have hnat' := hnat
            rw [show (coverSectionsIsoSpec Z).hom = Z.carrier.isoSpec.hom from rfl] at hnat'
            simpa only [← Category.assoc] using congrArg
              (fun f => Z.carrier.isoSpec.inv ≫ f) hnat'
      _ = Z.carrier.isoSpec.inv ≫
            ((F.map g).hom.left ≫ Z.carrier.isoSpec.hom) := rfl

  exact congrArg (fun f : CommRingCat.of Γ(Z.carrier, ⊤) ⟶
      CommRingCat.of Γ(Z.carrier, ⊤) => f.hom) h

/-- Naturality of the cover section map under composition. -/
theorem coverSectionsAlgHom_comp
    {X Z W : FiniteEtaleCover (Spec (CommRingCat.of R))}
    (f : X ⟶ Z) (g : Z ⟶ W) :
    (ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom
        (R := R) (X := X) (Z := W) (f ≫ g)) =
      (ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom
        (R := R) (X := X) (Z := Z) f).comp
      (ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom
        (R := R) (X := Z) (Z := W) g) := by
  ext x
  simp only [ABCBridge.AffineQuotientUniversalProperty.coverSectionsAlgHom,
    coverMorphismToSectionsAlgHom, AlgHom.comp_apply, Functor.map_comp, Over.comp_left]
  let A : Spec (CommRingCat.of Γ(X.carrier, ⊤)) ⟶
      Spec (CommRingCat.of Γ(W.carrier, ⊤)) :=
    X.carrier.isoSpec.inv ≫
      (Over.Hom.left ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map f) ≫
        Over.Hom.left ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map g)) ≫
      W.carrier.isoSpec.hom
  let B : Spec (CommRingCat.of Γ(X.carrier, ⊤)) ⟶
      Spec (CommRingCat.of Γ(Z.carrier, ⊤)) :=
    X.carrier.isoSpec.inv ≫
      Over.Hom.left ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map f) ≫
      Z.carrier.isoSpec.hom
  let C : Spec (CommRingCat.of Γ(Z.carrier, ⊤)) ⟶
      Spec (CommRingCat.of Γ(W.carrier, ⊤)) :=
    Z.carrier.isoSpec.inv ≫
      Over.Hom.left ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map g) ≫
      W.carrier.isoSpec.hom
  change (Spec.preimage A).hom x = (Spec.preimage B).hom ((Spec.preimage C).hom x)
  have hA : A = B ≫ C := by
    simp only [A, B, C, Category.assoc]
    erw [Iso.hom_inv_id_assoc (Z.carrier.isoSpec)
      (Over.Hom.left ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map g) ≫
        W.carrier.isoSpec.hom)]
    rfl
  have hpre : Spec.preimage A = Spec.preimage C ≫ Spec.preimage B := by
    rw [hA, Spec.preimage_comp]
  rw [hpre]
  rfl

section QuotientCover

variable [Finite G]

/-- The actual affine quotient cover of the acted cover underlying a
single-object diagram. -/
noncomputable def quotientCoverOfDiagram
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) :
    FiniteEtaleCover (Spec (CommRingCat.of R)) :=
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  let Z := F.obj (SingleObj.star G)
  letI : Algebra R Γ(Z.carrier, ⊤) := finiteEtaleCoverSectionsAlgebra R Z
  letI : MulSemiringAction G Γ(Z.carrier, ⊤) :=
    coverSectionsMulSemiringAction Z (actionOfDiagram F)
  letI : SMulCommClass G R Γ(Z.carrier, ⊤) :=
    coverSectionsSMulCommClass Z (actionOfDiagram F)
  letI : Algebra.Etale R Γ(Z.carrier, ⊤) := finiteEtaleCoverSections_etale Z
  letI : Module.Finite R Γ(Z.carrier, ⊤) := finiteEtaleCoverSections_finite Z
  affineQuotientCoverGeneral (R := R) (Γ(Z.carrier, ⊤)) G

/-- The quotient projection as a morphism of finite etale covers. -/
noncomputable def quotientProjectionOfDiagram
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) :
    F.obj (SingleObj.star G) ⟶ quotientCoverOfDiagram (R := R) (G := G) F :=
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  let Z := F.obj (SingleObj.star G)
  letI : Algebra R Γ(Z.carrier, ⊤) := finiteEtaleCoverSectionsAlgebra R Z
  letI : MulSemiringAction G Γ(Z.carrier, ⊤) :=
    coverSectionsMulSemiringAction Z (actionOfDiagram F)
  letI : SMulCommClass G R Γ(Z.carrier, ⊤) :=
    coverSectionsSMulCommClass Z (actionOfDiagram F)
  letI : Module.Finite R Γ(Z.carrier, ⊤) := finiteEtaleCoverSections_finite Z
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk
    (X := Z) (Y := quotientCoverOfDiagram (R := R) (G := G) F)
    (LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry.coverQuotientProjection
      (R := R) (G := G) Z)
    (by
      exact LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry.coverQuotientProjection_over
        (R := R) (G := G) Z (ABCBridge.IsospecSectionsCoherence.isoSpec_sectionsAlgebraMap Z))

/-- The quotient projection is invariant under the diagram action. -/
theorem quotientProjectionOfDiagram_invariant
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) (g : G) :
    F.map g ≫ quotientProjectionOfDiagram (R := R) (G := G) F =
      quotientProjectionOfDiagram (R := R) (G := G) F := by
  apply ObjectProperty.hom_ext
  ext
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  let Z := F.obj (SingleObj.star G)
  letI : Algebra R Γ(Z.carrier, ⊤) := finiteEtaleCoverSectionsAlgebra R Z
  letI : MulSemiringAction G Γ(Z.carrier, ⊤) :=
    coverSectionsMulSemiringAction Z (actionOfDiagram F)
  letI : SMulCommClass G R Γ(Z.carrier, ⊤) :=
    coverSectionsSMulCommClass Z (actionOfDiagram F)
  letI : Module.Finite R Γ(Z.carrier, ⊤) := finiteEtaleCoverSections_finite Z
  change (F.map g).hom.left ≫
      LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry.coverQuotientProjection
        (R := R) (G := G) Z =
    LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry.coverQuotientProjection
      (R := R) (G := G) Z
  rw [← coverAutSchemeIso_action_hom (R := R) F g]
  change (coverAutSchemeIso Z (actionOfDiagram F) g).hom ≫
      (Z.carrier.isoSpec.hom ≫ affineFixedPointQuotientMap R Γ(Z.carrier, ⊤) G) =
    Z.carrier.isoSpec.hom ≫ affineFixedPointQuotientMap R Γ(Z.carrier, ⊤) G
  have hnat := coverSectionsSpecAut_agrees Z (actionOfDiagram F) g
  have hgroup : (coverSectionsSpecAut Z (actionOfDiagram F) g).hom =
      groupActionSpecAut (A := Γ(Z.carrier, ⊤)) (G := G) g⁻¹ := by
    unfold coverSectionsSpecAut groupActionSpecAut groupActionRingEquiv
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    ext x
    change coverSectionsRingEquiv Z (actionOfDiagram F) g x =
      coverSectionsRingEquiv Z (actionOfDiagram F) ((g⁻¹)⁻¹) x
    rw [inv_inv]
  have hnat' : Z.carrier.isoSpec.hom ≫
        groupActionSpecAut (A := Γ(Z.carrier, ⊤)) (G := G) g⁻¹ =
      (coverAutSchemeIso Z (actionOfDiagram F) g).hom ≫ Z.carrier.isoSpec.hom := by
    simpa [coverSectionsIsoSpec, hgroup] using hnat
  rw [← Category.assoc, ← hnat', Category.assoc,
    groupActionSpecAut_comp_affineFixedPointQuotientMap]

/-- The action cocone associated to the affine quotient cover of a
single-object diagram. -/
noncomputable def actionCoconeOfDiagram
    (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R))) :
    GlobalActionCoconeData (Spec (CommRingCat.of R)) G F where
  quotient := quotientCoverOfDiagram (R := R) (G := G) F
  proj := quotientProjectionOfDiagram (R := R) (G := G) F
  proj_invariant := quotientProjectionOfDiagram_invariant (R := R) (G := G) F

end QuotientCover

end ABCBridge.AffineBaseFiniteEtaleQuotients
