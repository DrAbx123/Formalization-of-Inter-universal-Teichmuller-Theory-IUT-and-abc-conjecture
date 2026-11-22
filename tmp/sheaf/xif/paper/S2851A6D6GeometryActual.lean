import tmp.sheaf.xif.paper.S2848D6F6CompleteActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2848D6F6CompleteActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF



/-- The actual F6 hyperbolic orbicurve built from the complete D6 realization. -/
noncomputable def S2851HyperbolicOrbicurve :
    Iut.HyperbolicOrbicurve S2844D6F6BaseChangeActual.K :=
  realizedHyperbolicOrbicurve S2844D6F6BaseChangeActual.K S2848D6.fiber S2848D6.isStack
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

/-- The actual once-punctured geometric carrier for A6. -/
noncomputable def S2851Carrier : OncePuncturedGeometricCarrier S2844D6F6BaseChangeActual.K where
  curve := (S2844Punctured : PuncturedEllipticCurve S2844D6F6BaseChangeActual.K)
  involution := AddEquiv.neg _
  involution_eq_neg := fun _ => rfl
  fixes_puncture := by
    change -(0 : (S2844Punctured : PuncturedEllipticCurve S2844D6F6BaseChangeActual.K).curve.toProjective.Point) = 0
    exact neg_zero
  signature := oncePuncturedSignature
  signature_eq := rfl
  hyperbolic := oncePuncturedSignature_hyperbolic

/-- The actual SourceOncePuncturedGeometry for S2844Punctured and the D6 orbicurve. -/
noncomputable def S2851SourceOncePuncturedGeometry :
    SourceOncePuncturedGeometry
      (S2844Punctured : PuncturedEllipticCurve S2844D6F6BaseChangeActual.K)
      S2851HyperbolicOrbicurve where
  signature := oncePuncturedElliptic_eq_sourceTypeOneOne.symm

#check S2851HyperbolicOrbicurve
#check S2851Carrier
#check S2851SourceOncePuncturedGeometry
#print axioms S2851Carrier
#print axioms S2851SourceOncePuncturedGeometry

end LeanFormal.IUT.XiFPaper.S2851A6D6GeometryActual
end
