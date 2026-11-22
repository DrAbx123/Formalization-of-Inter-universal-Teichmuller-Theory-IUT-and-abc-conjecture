import tmp.sheaf.xif.paper.S2538AffineCoverEquivActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2538AffineCoverEquivActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S2541CoverHomToAlgActual

/-- F1: explicit map from a base cover hom to the corresponding algebra hom
(in the direction opposite to the cover map). -/
noncomputable def S2541CoverHomToAlg
    {C D : FiniteEtaleCover S2482AffineScheme} (φ : C ⟶ D) :
    (Opposite.unop (S2538AffineCoverEquiv.functor.obj D)) ⟶
      (Opposite.unop (S2538AffineCoverEquiv.functor.obj C)) :=
  (S2538AffineCoverEquiv.functor.map φ).unop

#check S2541CoverHomToAlg
#print axioms S2541CoverHomToAlg
end LeanFormal.IUT.XiFPaper.S2541CoverHomToAlgActual
end