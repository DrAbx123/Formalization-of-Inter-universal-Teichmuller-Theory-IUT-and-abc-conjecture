import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineBaseFiniteEtaleQuotients
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace Probe2073A

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Finite G]
variable (F : SingleObj G ⥤ FiniteEtaleCover (Spec (CommRingCat.of R)))

open ABCBridge.AffineBaseFiniteEtaleQuotients

/-- The acted cover. -/
abbrev Z : FiniteEtaleCover (Spec (CommRingCat.of R)) := F.obj (SingleObj.star G)

example : G →* CategoryTheory.Aut Z := actionOfDiagram F

section

variable [Fintype G] [DecidableEq G]

example : Algebra R Γ(Z.carrier, ⊤) := finiteEtaleCoverSectionsAlgebra R Z

example : MulSemiringAction G Γ(Z.carrier, ⊤) :=
  ABCBridge.CoverSectionsAction.coverSectionsMulSemiringAction Z (actionOfDiagram F)

example : SMulCommClass G R Γ(Z.carrier, ⊤) :=
  ABCBridge.CoverSectionsAction.coverSectionsSMulCommClass Z (actionOfDiagram F)

-- relation between the abstract action and the section-ring automorphism
example (g : G) :
    letI := ABCBridge.CoverSectionsAction.coverSectionsMulSemiringAction Z (actionOfDiagram F)
    MulSemiringAction.toRingEquiv G Γ(Z.carrier, ⊤) g =
      ABCBridge.CoverSectionsAction.coverSectionsRingEquiv Z (actionOfDiagram F) g⁻¹ := rfl

-- relation between specAction and coverSectionsSpecAut
example (g : G) :
    letI := finiteEtaleCoverSectionsAlgebra R Z
    letI := ABCBridge.CoverSectionsAction.coverSectionsMulSemiringAction Z (actionOfDiagram F)
    letI := ABCBridge.CoverSectionsAction.coverSectionsSMulCommClass Z (actionOfDiagram F)
    LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof.specAction
        (R := R) (G := G) (A := Γ(Z.carrier, ⊤)) g =
      (ABCBridge.CoverSectionsAction.coverSectionsSpecAut Z (actionOfDiagram F) g⁻¹).hom := by
  rfl

end

end Probe2073A
