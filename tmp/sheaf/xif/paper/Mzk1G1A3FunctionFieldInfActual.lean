/- A3 / F2.3 dual closure: R2 n is a fraction field of the curve's function field (chart-inf).

  Mirror of `Mzk1G1A3FunctionFieldFinalActual` (chart-0):
  * `chartInf_isAffineOpen` via `IsAffineOpen.image_of_isOpenImmersion` + `image_top_eq_opensRange`;
  * `chartInf_opensRange_nonempty` from `chartInfRing_isDomain` (Mzk1G1A3CurveDomainActual);
  * `isFractionRing_chartInf_functionField` via `agFunctionField_isFractionRing_of_isAffineOpen`
    and the chart-infinity section identification `chartInf_sections_ringEquiv`
    (Mzk1G1A3ChartInfSectionsActual) transported by
    `IsFractionRing.isFractionRing_iff_of_base_ringEquiv`.
  Header RECON: all ingredients already in the tree (no duplicate):
  Mzk1G1A3ChartInfSectionsActual (chartInf_sections_ringEquiv),
  Mzk1G1A3CurveDomainActual (chartInfRing_isDomain), Mzk1G1A3CurveIntegralActual
  (curve_isIntegral), Mzk1G1A3FunctionFieldFinalActual (curve_locallyNoetherian,
  curve_irreducibleSpace), AG02FunctionFieldActual (agFunctionField_isFractionRing_of_isAffineOpen).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3ChartInfSectionsActual
import tmp.sheaf.xif.paper.Mzk1G1A3FunctionFieldFinalActual
import tmp.sheaf.xif.paper.Mzk1G1A3CurveDomainActual
import tmp.sheaf.xif.paper.AG02FunctionFieldActual
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldInfActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartInfSectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveDomainActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldFinalActual
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual

variable (n : Nat)

/-- chart-∞ 开集是仿射开集。 -/
theorem chartInf_isAffineOpen : IsAffineOpen (fermatChartInfToCurve n).opensRange := by
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of (R2 n))).Opens) := isAffineOpen_top _
  have h := IsAffineOpen.image_of_isOpenImmersion (f := fermatChartInfToCurve n) (U := ⊤) hU
  simpa [Scheme.Hom.image_top_eq_opensRange] using h

/-- chart-∞ 开集非空（`R2 n` 是整环）。 -/
theorem chartInf_opensRange_nonempty (hn : 1 ≤ n) :
    Nonempty (fermatChartInfToCurve n).opensRange := by
  haveI : IsDomain (R2 n) := chartInfRing_isDomain n (by omega)
  haveI : Nonempty (PrimeSpectrum (R2 n)) := inferInstance
  obtain ⟨x⟩ := ‹Nonempty (PrimeSpectrum (R2 n))›
  exact ⟨(fermatChartInfToCurve n) x, ⟨x, rfl⟩⟩

section
variable [IrreducibleSpace (fermatCurveScheme n)]
variable [Nonempty (fermatChartInfToCurve n).opensRange]

/-- **F2.3 对偶（chart-∞）**：`R2 n` 的分数环是曲线的函数域。 -/
theorem isFractionRing_chartInf_functionField (hn : 1 ≤ n) :
    @IsFractionRing (R2 n) _ (fermatCurveScheme n).functionField _
      ((algebraMap Γ(fermatCurveScheme n, (fermatChartInfToCurve n).opensRange)
          (fermatCurveScheme n).functionField).comp
        (chartInf_sections_ringEquiv n).symm.toRingHom).toAlgebra := by
  haveI : IsIntegral (fermatCurveScheme n) := curve_isIntegral n (by omega)
  haveI : IsLocallyNoetherian (fermatCurveScheme n) := curve_locallyNoetherian n
  have hΓ : IsFractionRing Γ(fermatCurveScheme n, (fermatChartInfToCurve n).opensRange)
      (fermatCurveScheme n).functionField :=
    agFunctionField_isFractionRing_of_isAffineOpen _ (chartInf_isAffineOpen n)
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
    (R := ↥Γ(fermatCurveScheme n, (fermatChartInfToCurve n).opensRange))
    (S := ↥(fermatCurveScheme n).functionField)
    (P := R2 n)
    (chartInf_sections_ringEquiv n)).mp hΓ

end

#print axioms chartInf_isAffineOpen
#print axioms chartInf_opensRange_nonempty
#print axioms isFractionRing_chartInf_functionField

end LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldInfActual
