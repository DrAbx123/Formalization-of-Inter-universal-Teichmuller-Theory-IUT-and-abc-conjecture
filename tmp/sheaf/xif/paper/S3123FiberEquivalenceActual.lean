import tmp.sheaf.xif.paper.S3123XKStackExtension
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension

namespace LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual

variable {l : PrimeGeFive}

noncomputable abbrev S3123BaseSpecMap :
    Spec (CommRingCat.of (S1280Arithmetic l).K) ⟶
      Spec (CommRingCat.of (S1280Arithmetic l).F) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (S1280Arithmetic l).F (S1280Arithmetic l).K))

noncomputable abbrev S3123Left : Iut.EtaleStackPseudofunctor (S1280Arithmetic l).K :=
  Iut.schemeRepresentableEtalePseudofunctor (S1280Arithmetic l).K
    (S3123BaseChangedScheme (l := l))

noncomputable abbrev S3123Right : Iut.EtaleStackPseudofunctor (S1280Arithmetic l).K :=
  Pseudofunctor.comp
    (schemeRestrictScalarsPseudofunctor
      (S1280Arithmetic l).F (S1280Arithmetic l).K)
    (S1536XF (l := l)).stack.fiber

noncomputable def S3123FiberApp
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123Left (l := l)).obj U ⟶ (S3123Right (l := l)).obj U :=
  (Discrete.functor (fun P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l) =>
    Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
      (Opposite.unop U.as) (S1419AffineOver (l := l))).symm P))).toCatHom

#check S3123FiberApp

end LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
end
