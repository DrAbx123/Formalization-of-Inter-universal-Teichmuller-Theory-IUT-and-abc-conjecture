import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual

noncomputable section
set_option maxHeartbeats 4000000
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual

universe u
variable (R : Type u) [CommRing R]

-- variant 1: plain
example (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (unitApp R A).hom.unop.hom = CommAlgCat.ofHom (sectionsAlgEquiv R A.unop) := rfl

-- variant 2: ascription
example (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :
    (unitApp R A).hom.unop.hom =
      CommAlgCat.ofHom (sectionsAlgEquiv R A.unop :
        coverSections R ((algToCover R).obj A) →ₐ[R] A.unop.obj) := rfl

-- variant 3: element level apply
example (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ)
    (y : ↑(Opposite.unop ((algToCover R ⋙ coverToAlg R).obj A)).obj) :
    (CommAlgCat.Hom.hom (unitApp R A).hom.unop.hom) y =
      (Scheme.ΓSpecIso (CommRingCat.of A.unop.obj)).hom.hom y := rfl

-- variant 4: element level with ring equiv
example (A : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ)
    (y : ↑(Opposite.unop ((algToCover R ⋙ coverToAlg R).obj A)).obj) :
    (CommAlgCat.Hom.hom (unitApp R A).hom.unop.hom) y =
      (Scheme.ΓSpecIso (CommRingCat.of A.unop.obj)).commRingCatIsoToRingEquiv y := rfl

end LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
