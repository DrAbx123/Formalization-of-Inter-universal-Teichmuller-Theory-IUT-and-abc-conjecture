import tmp.sheaf.xif.paper.Mzk1G1A3ChartSectionsActual
import tmp.sheaf.xif.paper.Mzk1G1A3FunctionFieldFinalActual
import tmp.sheaf.xif.paper.Mzk1G1A3CurveIntegralActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Tactic
/-!
# F4: `P_i|_Y` as a function-field element (chart-0 sections → germs)

`Mzk1G1A3ChartSectionsActual.chart0_sections_ringEquiv` identifies `Γ(Y_n, chart0Open)`
with `R n`; evaluating `P` at `psiChart0Coord n T` and transporting back gives a section,
and `Scheme.germToFunctionField` gives the function-field element.

**Instance discipline** (Lead diagnosis): `X.functionField` is an abbrev requiring
`[IrreducibleSpace X]`, so the instance must be a **parameter of the definition** (not a
`haveI` in the body): `chart0PolyFunctionField` takes `[IrreducibleSpace (fermatCurveScheme n)]`
and `[Nonempty (chart0Open n)]`.  Use sites instantiate them by
`letI : IrreducibleSpace (fermatCurveScheme n) := irreducibleSpace_of_isIntegral (X := fermatCurveScheme n)`
and `letI : Nonempty (chart0Open n) := chart0_opensRange_nonempty n hn`.

## Reuse / donor check (2026-11-17)
* `chart0_sections_ringEquiv` (DONE); `chart0_opensRange_nonempty` (DONE);
* `psiChart0Coord` (DONE); `irreducibleSpace_of_isIntegral` (Mathlib Properties:262);
* `curve_isIntegral` (DONE).
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4FunctionFieldActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartSectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual

abbrev chart0Open (n : Nat) : (fermatCurveScheme n).Opens :=
  (fermatChart0ToCurve n).opensRange

noncomputable def chart0PolySection (n : Nat) (T : Finset ℚ)
    (P : MvPolynomial (Fin 3) ℚ) :
    Γ(fermatCurveScheme n, chart0Open n) :=
  (chart0_sections_ringEquiv n).symm (MvPolynomial.aeval ![psiChart0Coord n T, 1, 1] P)

/-- Function-field element `P_i|_Y`; instances are explicit parameters (abbrev statement). -/
noncomputable def chart0PolyFunctionField (n : Nat)
    [IrreducibleSpace (fermatCurveScheme n)] [Nonempty (chart0Open n)]
    (T : Finset ℚ) (P : MvPolynomial (Fin 3) ℚ) :
    (fermatCurveScheme n).functionField :=
  (fermatCurveScheme n).germToFunctionField (chart0Open n) (chart0PolySection n T P)

/-- The germ form (definitional). -/
theorem chart0PolyFunctionField_eq_germ (n : Nat)
    [IrreducibleSpace (fermatCurveScheme n)] [Nonempty (chart0Open n)]
    (T : Finset ℚ) (P : MvPolynomial (Fin 3) ℚ) :
    chart0PolyFunctionField n T P =
      (fermatCurveScheme n).germToFunctionField (chart0Open n) (chart0PolySection n T P) :=
  rfl

#print axioms chart0PolyFunctionField_eq_germ
end LeanFormal.IUT.XiFPaper.HTF4FunctionFieldActual
end