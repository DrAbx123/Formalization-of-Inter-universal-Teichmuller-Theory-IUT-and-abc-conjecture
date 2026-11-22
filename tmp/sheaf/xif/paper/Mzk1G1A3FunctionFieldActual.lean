/- A3 / F2.3 (partial batch): chart-0 open is affine; main transport recorded as obligation.

  PROVED here: `chart0_isAffineOpen : IsAffineOpen (fermatChart0ToCurve n).opensRange`
  (`IsAffineOpen.image_of_isOpenImmersion` + `Scheme.Hom.image_top_eq_opensRange`).

  The remaining step `IsFractionRing (R n) (Y.functionField)` is blocked at the following
  exact points (recorded for the next batch; see coord/EXPLICIT-PARAM-AUDIT-GRACE.md §F2.3):
  (i) after `haveI : IsIntegral (fermatCurveScheme n) := curve_isIntegral n hn` (DONE
      11:49:19) typeclass search still fails to synthesize `IrreducibleSpace
      (fermatCurveScheme n)` for `Scheme.functionField` -- must be added explicitly via
      `(isIntegral_iff_irreducibleSpace_and_isReduced _).mp ‹IsIntegral _›` (or the extending
      instance if present in this Mathlib version);
  (ii) `algebraMap Γ(...) (functionField)` and the `IsFractionRing` transport additionally ask
      for `IsLocallyNoetherian (fermatCurveScheme n)` in this Mathlib version; no instance for
      the glued Fermat curve over ℚ is in the tree, so it must be built from
      `Scheme.GlueData.isLocallyNoetherian` (charts are quotients of `MvPolynomial` over a
      field, hence Noetherian) -- a separate ~1-batch obligation.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3ChartSectionsActual
import tmp.sheaf.xif.paper.Mzk1G1A3CurveIntegralActual
import tmp.sheaf.xif.paper.AG02FunctionFieldActual
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartSectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual

variable (n : Nat)

/-- chart-0 开集是仿射开集。 -/
theorem chart0_isAffineOpen : IsAffineOpen (fermatChart0ToCurve n).opensRange := by
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of (R n))).Opens) := isAffineOpen_top _
  have h := IsAffineOpen.image_of_isOpenImmersion (f := fermatChart0ToCurve n) (U := ⊤) hU
  simpa [Scheme.Hom.image_top_eq_opensRange] using h

#print axioms chart0_isAffineOpen

end LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldActual
