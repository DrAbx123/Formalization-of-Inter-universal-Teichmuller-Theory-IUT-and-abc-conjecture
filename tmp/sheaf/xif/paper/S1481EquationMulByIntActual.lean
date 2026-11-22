import tmp.sheaf.xif.paper.S1430MulByIntBasicActual
import tmp.sheaf.xif.paper.S1452ZSMulEvalBridgeActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
/-! # S1481: exact first field for EquationMulByInt
S1430 defines EquationMulByInt but does not inhabit it.  The missing TauCeti
input is the full n-th ZSMul evaluation at the generic point with Y=omega and
Z=psi.  It is recorded as the exact Prop S1481OmegaZSMulBridge, not assumed.
Dependency table:
  S1430 genericX/genericY/genericPoint/equation  -> actual
  S1410 omega/psic                               -> actual definitions
  S1452 full ZSMul bridge (X=Phi,Y,Z=psi)        -> exact network input
  Y=omega (TauCeti zsmul_eq_smulEval full form)  -> exact first field
  IsEllipticNet(normEDS)                          -> Mathlib v4.32.2 TODO
No vendor, no assumption of EquationMulByInt. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1481EquationMulByIntActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open TauCeti.Isogeny
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
/-- Exact first field: full n-th ZSMul evaluation at the generic point with
middle coordinate omega and third coordinate psi. -/
def S1481OmegaZSMulBridge (n : ℤ) : Prop :=
  ∃ (Y : W.FunctionField)
    (h : (W⁄W.FunctionField).toAffine.Nonsingular
      (genericX W) (genericY W)),
    Y = omegaFunctionField W n ∧
    (n • (genericPoint W).toJacobian).point =
      ⟦![((W.Φ n).map (algebraMap F W.FunctionField)).eval (genericX W), Y, psiFunctionField W n]⟧
/-- The exact first field supplies the affine X/Y coordinates used by
EquationMulByInt.  The remaining polynomial equation check is TauCeti's
equation_mulByInt; no inhabitant is asserted here. -/
def S1481FirstField (n : ℤ) : Prop :=
  S1481OmegaZSMulBridge W n
#check EquationMulByInt
#check mulByIntX
#check mulByIntY
end LeanFormal.IUT.XiFPaper.S1481EquationMulByIntActual
