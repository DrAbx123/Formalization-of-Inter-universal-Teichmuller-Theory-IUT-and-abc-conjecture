/- A3 / F2.3: chart-0 section identification Γ(curve, chart0Open) ≃+* R n (approved batch).

  Route F2.3: for the function-field bridge we need the chart-0 ring as the sections of the
  curve over the chart-0 open. `IsOpenImmersion.ΓIso` identifies the global sections of
  `Spec (R n)` with the sections of the curve over `(fermatChart0ToCurve n).opensRange`, and
  `Scheme.ΓSpecIso` identifies `Γ(Spec (R n), ⊤)` with `R n`. The chart-∞ dual is analogous.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartSectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

variable (n : Nat)

/-- **chart-0 截面识别（iso 形式）**：`Γ(curve, chart0Open) ≅ of (R n)`。 -/
noncomputable def chart0_sections_iso :
    Γ(fermatCurveScheme n, (fermatChart0ToCurve n).opensRange) ≅ CommRingCat.of (R n) :=
  (fermatCurveScheme n).presheaf.mapIso
      (Iso.op (eqToIso (by simp :
        (fermatChart0ToCurve n).opensRange ⊓ (⊤ : (fermatCurveScheme n).Opens) =
          (fermatChart0ToCurve n).opensRange)))
    ≪≫ (IsOpenImmersion.ΓIso (fermatChart0ToCurve n) ⊤).symm
    ≪≫ (Spec (CommRingCat.of (R n))).presheaf.mapIso
          (Iso.op (eqToIso (by simp :
            (⊤ : (Spec (CommRingCat.of (R n))).Opens) =
              (fermatChart0ToCurve n) ⁻¹ᵁ (⊤ : (fermatCurveScheme n).Opens))))
    ≪≫ Scheme.ΓSpecIso (CommRingCat.of (R n))
/-- **chart-0 截面识别（环同构形式）**：`Γ(curve, chart0Open) ≃+* R n`。 -/
noncomputable def chart0_sections_ringEquiv :
    Γ(fermatCurveScheme n, (fermatChart0ToCurve n).opensRange) ≃+* R n :=
  (chart0_sections_iso n).commRingCatIsoToRingEquiv

#print axioms chart0_sections_ringEquiv

end LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartSectionsActual