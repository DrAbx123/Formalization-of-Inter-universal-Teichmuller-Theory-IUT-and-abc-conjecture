import tmp.sheaf.xif.paper.S2072HasQuotientsActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFixedPointDescNormalForm

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2087Probe2

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

end Inst

end LeanFormal.IUT.XiFPaper.S2087Probe2
