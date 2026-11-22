import tmp.sheaf.xif.paper.S2787ClauseB37Actual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2789E37OrbicurveSignActual

/-- The concrete label `l = 5`. -/
noncomputable def S2789Label : PrimeGeFive :=
  ⟨5, by norm_num, by norm_num⟩

/-- The actual E37 arithmetic data over Q(i). -/
noncomputable def S2789Arithmetic : InitialThetaArithmeticData S2789Label :=
  S2787Arithmetic (fiveLabel := S2789Label)

local instance : Field S2789Arithmetic.F := S2789Arithmetic.fieldF

/-- The actual E37 punctured elliptic curve over Q(i), with the projective
zero as its explicit puncture. -/
noncomputable def S2789Curve : PuncturedEllipticCurve S2789Arithmetic.F where
  curve := (S2789Arithmetic.curve).curve
  isElliptic := (S2789Arithmetic.curve).isElliptic
  puncture := 0

/-- The actual elliptic -1 involution on the projective points of E37. -/
noncomputable def S2789Involution :
    S2789Curve.curve.toProjective.Point ≃+ S2789Curve.curve.toProjective.Point :=
  AddEquiv.neg _

/-- Real once-punctured geometric carrier for E37/Q(i): actual curve, actual
involution, actual hyperbolic signature. -/
noncomputable def S2789Carrier : OncePuncturedGeometricCarrier S2789Arithmetic.F where
  curve := S2789Curve
  involution := S2789Involution
  involution_eq_neg := fun _ => rfl
  fixes_puncture := by
    change -(0 : S2789Curve.curve.toProjective.Point) = 0
    exact neg_zero
  signature := oncePuncturedSignature
  signature_eq := rfl
  hyperbolic := oncePuncturedSignature_hyperbolic

theorem S2789Carrier_signature :
    S2789Carrier.signature = Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

theorem S2789Carrier_signature_sourceTypeOneOne :
    S2789Carrier.signature = sourceTypeOneOne := by
  rw [S2789Carrier_signature]
  exact oncePuncturedElliptic_eq_sourceTypeOneOne.symm

/-- Conditional actual `HyperbolicOrbicurve` for E37/Q(i), from the explicit
missing D6 geometric realization. -/
noncomputable def S2789HyperbolicOrbicurve
    (D : MissingD6GeometricRealization S2789Arithmetic.F) :
    Iut.HyperbolicOrbicurve S2789Arithmetic.F :=
  realizedHyperbolicOrbicurve S2789Arithmetic.F D.fiber D.isStack
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

theorem S2789HyperbolicOrbicurve_signature
    (D : MissingD6GeometricRealization S2789Arithmetic.F) :
    (S2789HyperbolicOrbicurve D).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

/-- Conditional `SourceOncePuncturedGeometry` for the E37 curve and the
conditional orbicurve. -/
noncomputable def S2789SourceOncePuncturedGeometry
    (D : MissingD6GeometricRealization S2789Arithmetic.F) :
    SourceOncePuncturedGeometry S2789Curve (S2789HyperbolicOrbicurve D) where
  signature := by
    rw [S2789HyperbolicOrbicurve_signature]
    exact oncePuncturedElliptic_eq_sourceTypeOneOne.symm

#check S2789Label
#check S2789Arithmetic
#check S2789Curve
#check S2789Involution
#check S2789Carrier
#check S2789Carrier_signature
#check S2789Carrier_signature_sourceTypeOneOne
#check S2789HyperbolicOrbicurve
#check S2789SourceOncePuncturedGeometry
#print axioms S2789Carrier_signature_sourceTypeOneOne
#print axioms S2789SourceOncePuncturedGeometry

end LeanFormal.IUT.XiFPaper.S2789E37OrbicurveSignActual
end
