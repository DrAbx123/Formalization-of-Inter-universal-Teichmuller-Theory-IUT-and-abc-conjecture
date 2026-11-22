import tmp.sheaf.xif.paper.S2072HasQuotientsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2087ProbeInspect

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open ABCBridge.AffineBaseFiniteEtaleQuotients
open ABCBridge.CoverSectionsAction
open ABCBridge.AffineQuotientUniversalProperty

universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Finite G]
variable (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)))

local instance instFintype : Fintype G := Fintype.ofFinite G
local instance instDecEq : DecidableEq G := Classical.decEq G
local instance instAlg : Algebra R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  finiteEtaleCoverSectionsAlgebra R (F.obj (SingleObj.star G))
local instance instAct : MulSemiringAction G Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  coverSectionsMulSemiringAction (F.obj (SingleObj.star G)) (actionOfDiagram F)
local instance instSMul : SMulCommClass G R Γ((F.obj (SingleObj.star G)).carrier, ⊤) :=
  coverSectionsSMulCommClass (F.obj (SingleObj.star G)) (actionOfDiagram F)

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

example (s : Cocone F) (g : G) :
    coverSectionsAlgHom (R := R) (X := srcCover F) (Z := s.pt)
        (F.map g ≫ s.ι.app (SingleObj.star G)) =
      (coverSectionsAlgHom (R := R) (X := srcCover F) (Z := srcCover F) (F.map g)).comp
        (coverSectionsAlgHom (R := R) (X := srcCover F) (Z := s.pt) (s.ι.app (SingleObj.star G))) :=
  coverSectionsAlgHom_comp (R := R) (X := srcCover F) (Z := srcCover F) (W := s.pt)
    (F.map g) (s.ι.app (SingleObj.star G))

example (s : Cocone F) (g : G) :
    phi F s = (coverSectionsAlgHom (R := R) (X := srcCover F) (Z := srcCover F) (F.map g)).comp (phi F s) := by
  have hinv := cocone_inv (R := R) (G := G) F s g
  have hcomp := coverSectionsAlgHom_comp (R := R)
    (X := srcCover F) (Z := srcCover F) (W := s.pt)
    (F.map g) (s.ι.app (SingleObj.star G))
  -- try simp only
  simpa only [phi, hinv] using hcomp

end LeanFormal.IUT.XiFPaper.S2087ProbeInspect
