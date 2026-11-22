import tmp.sheaf.xif.paper.S2482QiCurveActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open CategoryTheory
open AlgebraicGeometry
open scoped SpecOfNotation

abbrev S2482AffinePolynomial : MvPolynomial (Fin 2) F :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial S2482Curve

abbrev S2482CoordinateRing : Type :=
  MvPolynomial (Fin 2) F ⧸ Ideal.span {S2482AffinePolynomial}

abbrev S2482AffineScheme : Scheme :=
  Spec (CommRingCat.of S2482CoordinateRing)

abbrev S2482AffineOver : Iut.SchemeOverField F :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)))

theorem S2482RepresentableIsStack :
    (Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver).IsStack
      (Iut.SchemeOverField.etaleTopology F) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology F)
      (yoneda.obj S2482AffineOver) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := F) S2482AffineOver)
  change (discretePseudo (C := Iut.SchemeOverField F)
    (yoneda.obj S2482AffineOver)).IsStack
      (Iut.SchemeOverField.etaleTopology F)
  exact DiscreteSheafStack.discretePseudo_isStack
    (P := yoneda.obj S2482AffineOver) hP

noncomputable def S2482Orbicurve : Iut.HyperbolicOrbicurve F :=
  realizedHyperbolicOrbicurve F
    (Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver)
    S2482RepresentableIsStack
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

theorem S2482Orbicurve_signature :
    S2482Orbicurve.signature = Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

noncomputable def S2482OncePuncturedGeometry :
    InitialThetaSource.SourceOncePuncturedGeometry S2482PuncturedCurve S2482Orbicurve where
  signature := by
    rw [S2482Orbicurve_signature]
    rfl

#check S2482Orbicurve
#check S2482OncePuncturedGeometry
#print axioms S2482Orbicurve
#print axioms S2482OncePuncturedGeometry

end LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual

end