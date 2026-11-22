/- A3 / F2.3 dual: chart-infinity section identification Gamma(curve, chartInfOpen) = R2 n.

  Mirror of `Mzk1G1A3ChartSectionsActual` (chart-0): `IsOpenImmersion.ΓIso` identifies the
  global sections of `Spec (R2 n)` with the sections over `(fermatChartInfToCurve n).opensRange`,
  and `Scheme.ΓSpecIso` identifies `Γ(Spec (R2 n), ⊤)` with `R2 n`.
  Header RECON: no existing chart-infinity section identification found by grep
  (`GammaSpecIso`/`ΓIso` used only for chart-0 in Mzk1G1A3ChartSectionsActual); the generic
  Mathlib donors are `IsOpenImmersion.ΓIso` and `Scheme.ΓSpecIso`. No duplicate.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3ChartSectionsActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartInfSectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartSectionsActual

variable (n : Nat)

/-- **chart-∞ 截面识别（iso 形式）**：`Γ(curve, chartInfOpen) ≅ of (R2 n)`。 -/
noncomputable def chartInf_sections_iso :
    Γ(fermatCurveScheme n, (fermatChartInfToCurve n).opensRange) ≅ CommRingCat.of (R2 n) :=
  (fermatCurveScheme n).presheaf.mapIso
      (Iso.op (eqToIso (by simp :
        (fermatChartInfToCurve n).opensRange ⊓ (⊤ : (fermatCurveScheme n).Opens) =
          (fermatChartInfToCurve n).opensRange)))
    ≪≫ (IsOpenImmersion.ΓIso (fermatChartInfToCurve n) ⊤).symm
    ≪≫ (Spec (CommRingCat.of (R2 n))).presheaf.mapIso
          (Iso.op (eqToIso (by simp :
            (⊤ : (Spec (CommRingCat.of (R2 n))).Opens) =
              (fermatChartInfToCurve n) ⁻¹ᵁ (⊤ : (fermatCurveScheme n).Opens))))
    ≪≫ Scheme.ΓSpecIso (CommRingCat.of (R2 n))

/-- **chart-∞ 截面识别（环同构形式）**：`Γ(curve, chartInfOpen) ≃+* R2 n`。 -/
noncomputable def chartInf_sections_ringEquiv :
    Γ(fermatCurveScheme n, (fermatChartInfToCurve n).opensRange) ≃+* R2 n :=
  (chartInf_sections_iso n).commRingCatIsoToRingEquiv

#print axioms chartInf_sections_ringEquiv

end LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartInfSectionsActual
