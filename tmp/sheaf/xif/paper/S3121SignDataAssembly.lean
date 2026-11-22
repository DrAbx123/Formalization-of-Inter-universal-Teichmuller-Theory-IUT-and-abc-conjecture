import tmp.sheaf.xif.paper.S3121DiagramActual

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S3121SignDataActual
open LeanFormal.IUT.XiFPaper.S3121DiagramActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S3121SignDataAssembly

variable {l : PrimeGeFive}

structure S3121SignData where
  D : Iut.SignActionIndex ⥤ᵖ
    Iut.EtaleStackPseudofunctor (S1280Arithmetic l).F
  atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
    (S1536XF (l := l)).stack.fiber
  generator_identification :
    (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
      S3119NegEllipticInvolution (l := l)

noncomputable def S3121SignDataActual' : S3121SignData (l := l) where
  D := S3121Diagram (l := l)
  atBase := S3121AtBase (l := l)
  generator_identification := by
    let x : (S1742YS (F := (S1280Arithmetic l).F)
        (S1419AffineOver l)) ⟶
        (S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l)) :=
      S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
        (S3119NegOverHom (l := l))
    change ((𝟙 (S1742YS (F := (S1280Arithmetic l).F)
        (S1419AffineOver l)) ≫ x) ≫
        𝟙 (S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l))) ≅
      S3119NegEllipticInvolution (l := l)
    exact (Bicategory.rightUnitor
        (𝟙 (S1742YS (F := (S1280Arithmetic l).F)
          (S1419AffineOver l)) ≫ x)).trans
      (Bicategory.leftUnitor x)

#check S3121SignDataActual'
#print axioms S3121SignDataActual'

end LeanFormal.IUT.XiFPaper.S3121SignDataAssembly
end
