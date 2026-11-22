import tmp.sheaf.xif.paper.S2072HasQuotientsActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFixedPointDescNormalForm

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2087Probe3

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection
open LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open ABCBridge.AffineBaseFiniteEtaleQuotients
open ABCBridge.CoverSectionsAction
open ABCBridge.AffineQuotientUniversalProperty
open LeanFormal.IUT.XiFPaper.S2072HasQuotientsActual

universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Finite G]
variable (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)))

section Inst

local instance instFintype : Fintype G := Fintype.ofFinite G
local instance instDecEq : DecidableEq G := Classical.decEq G
local instance instAlg : Algebra R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSectionsAlgebra R (F.obj (SingleObj.star G))
local instance instAct : MulSemiringAction G Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  coverSectionsMulSemiringAction (F.obj (SingleObj.star G)) (actionOfDiagram F)
local instance instSMul : SMulCommClass G R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  coverSectionsSMulCommClass (F.obj (SingleObj.star G)) (actionOfDiagram F)
local instance instEt : Algebra.Etale R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSections_etale (F.obj (SingleObj.star G))
local instance instFin : Module.Finite R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSections_finite (F.obj (SingleObj.star G))

abbrev srcCover : FiniteEtaleCover (Spec (CommRingCat.of R)) := F.obj (SingleObj.star G)
abbrev srcSections : Type u := Γ((F.obj (SingleObj.star G)).carrier, ⊤)
abbrev qtCover : FiniteEtaleCover (Spec (CommRingCat.of R)) := quotientCoverOfDiagram (R := R) (G := G) F
abbrev qtProj : srcCover F ⟶ qtCover F := quotientProjectionOfDiagram (R := R) (G := G) F

theorem finiteEtaleCoverHom_ext {X Y : FiniteEtaleCover (Spec (CommRingCat.of R))}
    {f g : X ⟶ Y}
    (h : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left =
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map g).left) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact h

noncomputable def phi (s : Cocone F) : Γ(s.pt.carrier, ⊤) →ₐ[R] srcSections F :=
  coverSectionsAlgHom (R := R) (X := srcCover F) (Z := s.pt) (s.ι.app (SingleObj.star G))

theorem cocone_inv (s : Cocone F) (g : G) :
    F.map g ≫ s.ι.app (SingleObj.star G) = s.ι.app (SingleObj.star G) := by
  have h := s.ι.naturality (X := SingleObj.star G) (Y := SingleObj.star G) g
  rw [show ((Functor.const (SingleObj G)).obj s.pt).map g =
      𝟙 (((Functor.const (SingleObj G)).obj s.pt).obj (SingleObj.star G)) from rfl] at h
  rw [Category.comp_id] at h
  exact h

theorem ringEquiv_invariant (s : Cocone F) (h : G) (b : Γ(s.pt.carrier, ⊤)) :
    coverSectionsRingEquiv (srcCover F) (actionOfDiagram F) h (phi F s b) = phi F s b := by
  have hinv := cocone_inv (R := R) (G := G) F s h
  have hcomp := coverSectionsAlgHom_comp (R := R)
    (X := srcCover F) (Z := srcCover F) (W := s.pt)
    (F.map h) (s.ι.app (SingleObj.star G))
  rw [hinv] at hcomp
  have hb := AlgHom.congr_fun hcomp b
  have hmap := coverSectionsAlgHom_map_eq (R := R) (G := G) F h
  have hb' : (coverSectionsAlgHom (R := R) (X := srcCover F) (Z := srcCover F) (F.map h)) (phi F s b) =
      coverSectionsRingEquiv (srcCover F) (actionOfDiagram F) h (phi F s b) :=
    DFunLike.congr_fun hmap (phi F s b)
  exact (hb.trans hb').symm

theorem phi_invariant (s : Cocone F) (g : G) (b : Γ(s.pt.carrier, ⊤)) :
    groupActionRingEquiv (srcSections F) G g (phi F s b) = phi F s b := by
  have hsmul : g • (phi F s b) =
      coverSectionsRingEquiv (srcCover F) (actionOfDiagram F) g⁻¹ (phi F s b) :=
    coverSections_smul_def (srcCover F) (actionOfDiagram F) g (phi F s b)
  rw [show groupActionRingEquiv (srcSections F) G g (phi F s b) = g • (phi F s b) from rfl]
  rw [hsmul]
  exact ringEquiv_invariant (R := R) (G := G) F s g⁻¹ b

noncomputable def descPsi (s : Cocone F) :
    Γ(s.pt.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R (srcSections F) G :=
  Classical.choose
    (ABCBridge.AffineFixedPointDescNormalForm.exists_affineFixedPointLiftAlgHom
      (R := R) (A := srcSections F) (B := Γ(s.pt.carrier, ⊤)) (G := G)
      (phi F s) (phi_invariant (R := R) (G := G) F s))

theorem descPsi_spec (s : Cocone F) :
    (fixedPointInclusion R (srcSections F) G).comp (descPsi F s) = phi F s :=
  (Classical.choose_spec
    (ABCBridge.AffineFixedPointDescNormalForm.exists_affineFixedPointLiftAlgHom
      (R := R) (A := srcSections F) (B := Γ(s.pt.carrier, ⊤)) (G := G)
      (phi F s) (phi_invariant (R := R) (G := G) F s))).1

theorem descPsi_commutes (s : Cocone F) :
    (descPsi F s).toRingHom.comp (algebraMap R Γ(s.pt.carrier, ⊤)) =
      algebraMap R (fixedPointSubalgebra R (srcSections F) G) :=
  (Classical.choose_spec
    (ABCBridge.AffineFixedPointDescNormalForm.exists_affineFixedPointLiftAlgHom
      (R := R) (A := srcSections F) (B := Γ(s.pt.carrier, ⊤)) (G := G)
      (phi F s) (phi_invariant (R := R) (G := G) F s))).2

noncomputable def descF (s : Cocone F) :
    (qtCover F).carrier ⟶ s.pt.carrier :=
  ABCBridge.AffineFixedPointDescNormalForm.descSchemeMap
    (R := R) (A := srcSections F) (G := G) (Z := s.pt) (descPsi F s)

theorem descW (s : Cocone F) :
    descF F s ≫ s.pt.structureMap = (qtCover F).structureMap :=
  ABCBridge.AffineFixedPointDescNormalForm.descSchemeMap_structureMap
    (R := R) (A := srcSections F) (G := G) (Z := s.pt) (descPsi F s) (descPsi_commutes F s)

noncomputable def desc (s : Cocone F) : qtCover F ⟶ s.pt :=
  AffineLocalQuotientGluingConstruct.finiteEtaleCoverHomMk (descF F s) (descW F s)

theorem desc_underlying (s : Cocone F) :
    (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map (desc F s)).left = descF F s := rfl

theorem desc_fac (s : Cocone F) :
    qtProj F ≫ desc F s = s.ι.app (SingleObj.star G) := by
  apply finiteEtaleCoverHom_ext
  change (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map (qtProj F)).left ≫
      (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map (desc F s)).left =
    (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map
      (s.ι.app (SingleObj.star G))).left
  have hproj : (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map (qtProj F)).left =
      (srcCover F).carrier.isoSpec.hom ≫
        affineFixedPointQuotientMap R (srcSections F) G := rfl
  rw [hproj, desc_underlying]
  change ((srcCover F).carrier.isoSpec.hom ≫
        affineFixedPointQuotientMap R (srcSections F) G) ≫
      (Spec.map (CommRingCat.ofHom (descPsi F s).toRingHom) ≫ s.pt.carrier.isoSpec.inv) =
    (s.ι.app (SingleObj.star G)).hom.left
  have hcomp : affineFixedPointQuotientMap R (srcSections F) G ≫
      Spec.map (CommRingCat.ofHom (descPsi F s).toRingHom) =
      Spec.map (CommRingCat.ofHom (phi F s).toRingHom) := by
    rw [affineFixedPointQuotientMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hring : (fixedPointInclusionRingHom R (srcSections F) G).comp (descPsi F s).toRingHom =
        (phi F s).toRingHom := congrArg AlgHom.toRingHom (descPsi_spec F s)
    rw [hring]
  have hspec : Spec.map (CommRingCat.ofHom (phi F s).toRingHom) =
      (srcCover F).carrier.isoSpec.inv ≫
        (s.ι.app (SingleObj.star G)).hom.left ≫ s.pt.carrier.isoSpec.hom :=
    specMap_coverMorphismToSectionsAlgHom (R := R) (A := srcSections F)
      (X := srcCover F) (Z := s.pt) (srcCover F).carrier.isoSpec
      (s.ι.app (SingleObj.star G))
  calc
    ((srcCover F).carrier.isoSpec.hom ≫ affineFixedPointQuotientMap R (srcSections F) G) ≫
        (Spec.map (CommRingCat.ofHom (descPsi F s).toRingHom) ≫ s.pt.carrier.isoSpec.inv)
        = (srcCover F).carrier.isoSpec.hom ≫
            (affineFixedPointQuotientMap R (srcSections F) G ≫
              Spec.map (CommRingCat.ofHom (descPsi F s).toRingHom)) ≫
            s.pt.carrier.isoSpec.inv := by rw [Category.assoc, Category.assoc]
    _ = (srcCover F).carrier.isoSpec.hom ≫
            Spec.map (CommRingCat.ofHom (phi F s).toRingHom) ≫
            s.pt.carrier.isoSpec.inv := by rw [hcomp]
    _ = (srcCover F).carrier.isoSpec.hom ≫
            ((srcCover F).carrier.isoSpec.inv ≫
              (s.ι.app (SingleObj.star G)).hom.left ≫ s.pt.carrier.isoSpec.hom) ≫
            s.pt.carrier.isoSpec.inv := by rw [hspec]
    _ = (s.ι.app (SingleObj.star G)).hom.left := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end Inst

end LeanFormal.IUT.XiFPaper.S2087Probe3
