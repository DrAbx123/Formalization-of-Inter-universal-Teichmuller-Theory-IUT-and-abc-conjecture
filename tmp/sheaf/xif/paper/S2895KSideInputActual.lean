import tmp.sheaf.xif.paper.S2880CorrectedA6CoreNontrivialActual
import tmp.sheaf.xif.paper.S2855A6CoreFromD6ConditionalActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2880CorrectedA6CoreNontrivialActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2895KSideInputActual

/-- Minimal K-side input: the two scalar extensions determine xK and cK.
The equalities xK = result and cK = result are then definitional. -/
structure S2895KInput
    (xF cF : Iut.HyperbolicOrbicurve S2847A6.F) where
  xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K xF
  cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF

namespace S2895KInput

variable {xF cF : Iut.HyperbolicOrbicurve S2847A6.F}

/-- xK is the result of the x-side scalar extension. -/
noncomputable def xK (P : S2895KInput xF cF) : Iut.HyperbolicOrbicurve S2847A6.K :=
  P.xKExtension.result

/-- cK is the result of the c-side scalar extension. -/
noncomputable def cK (P : S2895KInput xF cF) : Iut.HyperbolicOrbicurve S2847A6.K :=
  P.cKExtension.result

/-- The xK equality is definitional in the minimal package. -/
theorem xK_eq_extension (P : S2895KInput xF cF) :
    P.xK = P.xKExtension.result := rfl

/-- The cK equality is definitional in the minimal package. -/
theorem cK_eq_extension (P : S2895KInput xF cF) :
    P.cK = P.cKExtension.result := rfl

end S2895KInput

/-- Extract the minimal K-side package from an S2880 input. -/
noncomputable def S2895KInput.ofS2880
    {signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2880Inputs signAction) :
    S2895KInput S2855HyperbolicOrbicurve I.cF where
  xKExtension := I.xKExtension
  cKExtension := I.cKExtension

/-- The extracted xK agrees with the S2880 field. -/
theorem S2895KInput.ofS2880_xK
    {signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2880Inputs signAction) :
    (S2895KInput.ofS2880 I).xK = I.xK :=
  I.xK_eq_extension.symm

/-- The extracted cK agrees with the S2880 field. -/
theorem S2895KInput.ofS2880_cK
    {signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2880Inputs signAction) :
    (S2895KInput.ofS2880 I).cK = I.cK :=
  I.cK_eq_extension.symm

#check S2895KInput
#check S2895KInput.xK
#check S2895KInput.cK
#check S2895KInput.ofS2880
#check S2895KInput.ofS2880_xK
#check S2895KInput.ofS2880_cK
#print axioms S2895KInput.ofS2880
#print axioms S2895KInput.ofS2880_xK

end LeanFormal.IUT.XiFPaper.S2895KSideInputActual
end