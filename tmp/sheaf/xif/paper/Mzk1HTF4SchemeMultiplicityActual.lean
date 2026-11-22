import tmp.sheaf.xif.paper.AG02bPrincipalDivisorActual
import Mathlib.Tactic
/-!
# F4 scheme-level multiplicity: principal divisor via the DVR order of vanishing

Route §8.3 needs `div(P|_Y)` with **multiplicities**, not just the reduced zero set.
Mathlib provides the order of vanishing at codimension-one points (`Scheme.ord`,
reused by `AG02FunctionFieldActual.agOrderOfVanishing`), and `AG02bPrincipalDivisorActual`
builds the principal divisor `principalDivisor f : AGCodimOnePoint X → ℤ`, whose
coefficient at `z` is `ord_z(f)` (a DVR valuation at codim-one points).

This file exposes that donor as the **scheme-level multiplicity layer** for F4:
* `schemePrincipalDivisor f` with coefficients `ord_z(f)`;
* multiplicativity `schemePrincipalDivisor (f*g) = ... + ...` (from `ord_mul`);
* the `F4SchemeDivisorData` package (nonzero function field element + its divisor).

## Reuse / donor check (2026-11-17)
* `AG02bPrincipalDivisorActual.principalDivisor` / `principalDivisor_mul`
  (`AG02FunctionFieldActual.agOrderOfVanishing` = `Scheme.ord`) — olean present;
* Mathlib `AlgebraicGeometry.OrderOfVanishing` (`Scheme.ord`, `ord_mul`, `ord_zero`).

**Explicit obligation**: the identification of `P_i|_Y` with a nonzero element of
`Y_n.functionField` (and its divisor with the reduced `divP` when the orders are 0/1) is
not supplied here; the local DVR order itself is the donor above.
F4 remains unclosed until that identification is made.
-/
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.HTF4SchemeMultiplicityActual
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual
open LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual

universe u
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- Scheme-level principal divisor: coefficient `ord_z(f)` at every codimension-one point. -/
noncomputable def schemePrincipalDivisor (f : X.functionField) : AGCodimOnePoint X → ℤ :=
  principalDivisor f

theorem schemePrincipalDivisor_zero :
    schemePrincipalDivisor (X := X) (0 : X.functionField) = 0 :=
  principalDivisor_zero

theorem schemePrincipalDivisor_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    schemePrincipalDivisor (X := X) (f * g) =
      schemePrincipalDivisor (X := X) f + schemePrincipalDivisor (X := X) g :=
  principalDivisor_mul hf hg

theorem schemePrincipalDivisor_coeff (f : X.functionField) (z : AGCodimOnePoint X) :
    schemePrincipalDivisor (X := X) f z = agOrderOfVanishing f z :=
  rfl

/-- F4 scheme divisor data: a nonzero function-field element (the class of `P_i|_Y`)
and its multiplicity divisor. -/
structure F4SchemeDivisorData where
  f : X.functionField
  f_ne_zero : f ≠ 0

def F4SchemeDivisorData.divisor (D : F4SchemeDivisorData (X := X)) : AGCodimOnePoint X → ℤ :=
  schemePrincipalDivisor D.f

theorem F4SchemeDivisorData.divisor_mul (D E : F4SchemeDivisorData (X := X)) :
    (⟨D.f * E.f, mul_ne_zero D.f_ne_zero E.f_ne_zero⟩ : F4SchemeDivisorData (X := X)).divisor =
      F4SchemeDivisorData.divisor D + F4SchemeDivisorData.divisor E :=
  schemePrincipalDivisor_mul D.f_ne_zero E.f_ne_zero

#print axioms schemePrincipalDivisor_mul
#print axioms F4SchemeDivisorData.divisor_mul
end LeanFormal.IUT.XiFPaper.HTF4SchemeMultiplicityActual
end