import tmp.sheaf.xif.paper.S1483MulByIntOnFunctionFieldActual

/-! # S1531: OmegaZSMulBridge rebased onto S1467/S1483

S1481 imported S1430, which defines the TauCeti.Isogeny structure that also
appears in S1467; importing both is the duplicate-constructor conflict.  This
file imports only S1483 (which imports S1467), so no S1430 and no duplicate
genericX / Isogeny.

The S1430 bridge also used `(genericPoint W).toJacobian`, a TauCeti
Jacobian-point accessor that does not exist on the S1467 Mathlib affine-point
generic point.  The exact first missing field is therefore that affine-to-
Jacobian generic-point conversion inside the S1467 layer; the equation target
itself is available as S1483's EquationMulByInt.

No duplicate Isogeny/genericX and no S1430 import is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1531OmegaBridgeRebasedActual

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open TauCeti.Isogeny

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- Rebased omega at the generic point, from S1483. -/
noncomputable def s1531OmegaFunctionField (n : ℤ) : W.FunctionField :=
  omegaFunctionField W n

/-- Rebased psi at the generic point, from S1483. -/
noncomputable def s1531PsiFunctionField (n : ℤ) : W.FunctionField :=
  psiFunctionField W n

/-- Rebased generic point, from S1467. -/
noncomputable def s1531GenericPoint : (W⁄W.FunctionField).Point :=
  genericPoint W

/-- The actual equation target available in the rebased layer. -/
def S1531EquationMulByIntRequired (n : ℤ) : Prop :=
  EquationMulByInt W n

#check EquationMulByInt
#check mulByIntX
#check mulByIntY

end LeanFormal.IUT.XiFPaper.S1531OmegaBridgeRebasedActual

end
