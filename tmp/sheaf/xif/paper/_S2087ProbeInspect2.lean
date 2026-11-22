import tmp.sheaf.xif.paper.S2072HasQuotientsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2087ProbeInspect2

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

abbrev srcCover : FiniteEtaleCover (Spec (CommRingCat.of R)) := F.obj (SingleObj.star G)

example (s : Cocone F) (g : G)
    (hinv : F.map g ≫ s.ι.app (SingleObj.star G) = s.ι.app (SingleObj.star G)) :
    coverSectionsAlgHom (R := R) (X := srcCover F) (Z := s.pt)
        (F.map g ≫ s.ι.app (SingleObj.star G)) =
      coverSectionsAlgHom (R := R) (X := srcCover F) (Z := s.pt) (s.ι.app (SingleObj.star G)) := by
  rw [hinv]

example (s : Cocone F) (g : G)
    (hinv : F.map g ≫ s.ι.app (SingleObj.star G) = s.ι.app (SingleObj.star G)) :
    @coverSectionsAlgHom R _ (srcCover F) s.pt
        (F.map g ≫ s.ι.app (SingleObj.star G)) =
      @coverSectionsAlgHom R _ (srcCover F) s.pt (s.ι.app (SingleObj.star G)) := by
  rw [hinv]

example (s : Cocone F) (g : G)
    (hinv : F.map g ≫ s.ι.app (SingleObj.star G) = s.ι.app (SingleObj.star G)) :
    (F.map g ≫ s.ι.app (SingleObj.star G) : srcCover F ⟶ s.pt) = s.ι.app (SingleObj.star G) := by
  rw [hinv]

end LeanFormal.IUT.XiFPaper.S2087ProbeInspect2
