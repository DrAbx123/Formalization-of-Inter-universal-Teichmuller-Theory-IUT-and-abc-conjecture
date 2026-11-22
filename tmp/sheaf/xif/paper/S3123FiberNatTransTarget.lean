import tmp.sheaf.xif.paper.S3123FiberEquivalenceActual
import Mathlib.CategoryTheory.Thin

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual

namespace LeanFormal.IUT.XiFPaper.S3123FiberNatTrans

variable {l : PrimeGeFive}

#check Adjunction.homEquiv_naturality_left
#check Adjunction.homEquiv_naturality_right
#check CategoryTheory.Cat.Hom.isoMk
#check CategoryTheory.Discrete.eqToHom

abbrev S3123FiberNatTransTarget {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) : Type :=
  ((S3123Left (l := l)).map g ≫ S3123FiberApp (l := l) b) ⟶
    (S3123FiberApp (l := l) a ≫ (S3123Right (l := l)).map g)

#check S3123FiberNatTransTarget

end LeanFormal.IUT.XiFPaper.S3123FiberNatTrans
end
