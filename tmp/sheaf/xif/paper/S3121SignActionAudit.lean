import tmp.sheaf.xif.paper.S3119NegInvolutionAttempt
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1742HomVcompActual

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3121SignActionAudit

variable {l : PrimeGeFive}

/-- Explicit diagram/equivalence/identification data needed for the sign action. -/
structure S3121SignData where
  D : Iut.SignActionIndex ⥤ᵖ
    Iut.EtaleStackPseudofunctor (S1280Arithmetic l).F
  atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
    (S1536XF (l := l)).stack.fiber
  generator_identification :
    (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
      S3119NegEllipticInvolution (l := l)

/-- Conditional actual sign action from the diagram data; inversion and
inversionSquared are actual from S3119. -/
noncomputable def S3121SignActionOf (I : S3121SignData (l := l)) :
    Iut.OrbicurveSignAction (S1536XF (l := l)) :=
  Iut.orbicurveSignActionOf (S1536XF (l := l)) I.D I.atBase
    (S3119NegEllipticInvolution (l := l)) I.generator_identification
    (S3119NegEllipticInvolution_squared (l := l))

/-- Exact nonemptiness target. -/
def S3121SignActionTarget : Prop :=
  Nonempty (Iut.OrbicurveSignAction (S1536XF (l := l)))

/-- Exact diagram target. -/
def S3121DiagramTarget : Prop :=
  Nonempty (S3121SignData (l := l))

#check S3121SignData
#check S3121SignActionOf
#check S3121SignActionTarget
#check S3121DiagramTarget
#check S1742StrongTransOfHom
#check S1742HomOfStrongTrans_vcomp
#check S1742HomOfStrongTrans_strongTransOfHom
#check S1742StrongTransIsoOfHom

end LeanFormal.IUT.XiFPaper.S3121SignActionAudit
end