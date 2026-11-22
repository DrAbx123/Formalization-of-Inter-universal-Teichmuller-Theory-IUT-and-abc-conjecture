import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.CategoryTheory.Comma.Over.Pullback
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed
import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

universe u

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation Pseudofunctor.StrongTrans Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123XKStackExtension

variable {l : PrimeGeFive}

abbrev S3123F := (S1280Arithmetic l).F
abbrev S3123K := (S1280Arithmetic l).K



noncomputable abbrev S3123BaseChange :
    Iut.SchemeOverField (S3123F (l := l)) ⥤
      Iut.SchemeOverField (S3123K (l := l)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (S3123F (l := l)) (S3123K (l := l)))))

noncomputable abbrev S3123BaseChangedScheme :
    Iut.SchemeOverField (S3123K (l := l)) :=
  (S3123BaseChange (l := l)).obj (S1419AffineOver (l := l))

theorem S3123BaseChangedIsStack :
    (Iut.schemeRepresentableEtalePseudofunctor (S3123K (l := l))
      (S3123BaseChangedScheme (l := l))).IsStack
      (Iut.SchemeOverField.etaleTopology (S3123K (l := l))) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology (S3123K (l := l)))
      (yoneda.obj (S3123BaseChangedScheme (l := l))) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf
        (F := S3123K (l := l)) (S3123BaseChangedScheme (l := l)))
  change (discretePseudo (C := Iut.SchemeOverField (S3123K (l := l)))
    (yoneda.obj (S3123BaseChangedScheme (l := l)))).IsStack
      (Iut.SchemeOverField.etaleTopology (S3123K (l := l)))
  exact LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual.DiscreteSheafStack.discretePseudo_isStack
    (P := yoneda.obj (S3123BaseChangedScheme (l := l))) hP

noncomputable def S3123Result : Iut.EtaleStackOverField (S3123K (l := l)) where
  fiber := Iut.schemeRepresentableEtalePseudofunctor (S3123K (l := l))
    (S3123BaseChangedScheme (l := l))
  isStack := S3123BaseChangedIsStack (l := l)

#check S3123BaseChange
#check S3123BaseChangedScheme
#check S3123Result


section
variable {l : PrimeGeFive}
variable [Bicategory (Iut.EtaleStackPseudofunctor (S1280Arithmetic l).K)]

/-- The fiber equivalence target, with the Bicategory structure supplied as a
section variable so that the type can be stated without synthesizing a
universe-polymorphic instance. -/
noncomputable def S3123FiberEquivalenceTarget : Type :=
  Bicategory.Equivalence
    (Iut.schemeRepresentableEtalePseudofunctor
      (S1280Arithmetic l).K (S3123BaseChangedScheme (l := l)))
    (Pseudofunctor.comp
      (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
      (S1536XF (l := l)).stack.fiber)

end

set_option pp.universes true in
#check @S3123FiberEquivalenceTarget


end LeanFormal.IUT.XiFPaper.S3123XKStackExtension
end
