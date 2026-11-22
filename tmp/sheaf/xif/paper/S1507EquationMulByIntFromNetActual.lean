import tmp.sheaf.xif.paper.S1491NormEDSNetActual
import tmp.sheaf.xif.paper.S1483MulByIntOnFunctionFieldActual

/-! # S1507: net input and the exact missing EquationMulByInt input.

S1491 provides IsEllipticNet.normEDS / isEllipticNet_ψ /
isEllipticNet_evalEval_ψ.  S1483 provides the generic-point division-polynomial
layer and EquationMulByInt.  This file records the remaining exact bridge
(full ZSMul evaluation at the generic point) and the already-proved generic
psi non-vanishing; it does NOT assume EquationMulByInt. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1507EquationMulByIntFromNetActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open TauCeti.Isogeny

universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- Generic-point psi non-vanishing, as proved in S1483. -/
theorem s1507_psiFunctionField_ne_zero {n : ℤ} (hn : (n : F) ≠ 0) :
    psiFunctionField W n ≠ 0 :=
  psiFunctionField_ne_zero W hn

/-- Exact EquationMulByInt target, not assumed. -/
def S1507EquationMulByIntRequired (n : ℤ) : Prop :=
  EquationMulByInt W n

/-- Exact missing nonzero input is already discharged from S1483 when
  (n : F) ≠ 0. -/
theorem s1507_genericPsiNonzero {n : ℤ} (hn : (n : F) ≠ 0) :
    psiFunctionField W n ≠ 0 :=
  s1507_psiFunctionField_ne_zero W hn

end LeanFormal.IUT.XiFPaper.S1507EquationMulByIntFromNetActual
end