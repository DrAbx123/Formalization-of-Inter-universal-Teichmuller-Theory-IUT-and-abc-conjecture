import tmp.sheaf.xif.paper.S3121SignDataActual

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S3121GeneratorIsoActual

variable {l : PrimeGeFive}

abbrev S3121GenX : Pseudofunctor.StrongTrans
    (S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l))
    (S1742YS (F := (S1280Arithmetic l).F) (S1419AffineOver l)) :=
  S1742StrongTransOfHom (F := (S1280Arithmetic l).F)
    (S3119NegOverHom (l := l))

lemma S3121GeneratorIso :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (show (S1536XF (l := l)).Hom (S1536XF (l := l)) from
        (𝟙 ≫ S3121GenX (l := l)) ≫ 𝟙)
      (S3119NegEllipticInvolution (l := l)) := by
  exact (Pseudofunctor.StrongTrans.rightUnitor
      (𝟙 ≫ S3121GenX (l := l))).trans
    (Pseudofunctor.StrongTrans.leftUnitor (S3121GenX (l := l)))

#check S3121GeneratorIso
#print axioms S3121GeneratorIso

end LeanFormal.IUT.XiFPaper.S3121GeneratorIsoActual
end
