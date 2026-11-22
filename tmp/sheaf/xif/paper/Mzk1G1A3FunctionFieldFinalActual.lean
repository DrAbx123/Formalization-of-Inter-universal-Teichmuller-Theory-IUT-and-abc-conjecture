/- A3 / F2.3 closure: locally Noetherian + irreducible instances, and the fraction-field bridge.

  `Scheme.functionField` carries an `[IrreducibleSpace X]` argument, hence the closure theorem
  takes the (proved) `IrreducibleSpace (fermatCurveScheme n)` and the (proved) nonempty chart-0
  open as instance arguments; consumers instantiate them with `curve_irreducibleSpace n hn`
  and `chart0_opensRange_nonempty n hn`. The explicit `Algebra` structure of the transport is
  from `IsFractionRing.isFractionRing_iff_of_base_ringEquiv`. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3FunctionFieldActual
import tmp.sheaf.xif.paper.Mzk1G1A3CurveIntegralActual
import tmp.sheaf.xif.paper.AG02FunctionFieldActual
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartSectionsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldActual
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual

variable (n : Nat)

/-- **曲线在 ℚ 上局部 Noetherian**（两 chart 的环是 `MvPolynomial (Fin 2) ℚ` 的商）。 -/
theorem curve_locallyNoetherian : IsLocallyNoetherian (fermatCurveScheme n) := by
  have hU : ∀ i, IsLocallyNoetherian ((fermatTwoChartGlueData n).U i) := by
    intro i
    obtain ⟨b⟩ := i
    cases b
    · change IsLocallyNoetherian (fermatChart0Scheme n)
      infer_instance
    · change IsLocallyNoetherian (fermatChartInfScheme n)
      infer_instance
  rw [fermatCurveScheme_eq_glued n]
  refine (isLocallyNoetherian_iff_openCover (fermatTwoChartGlueData n).openCover).mpr ?_
  intro i
  have h := hU i
  change IsLocallyNoetherian ((fermatTwoChartGlueData n).U i)
  exact h

/-- **曲线不可约**（由 `IsIntegral`）。 -/
theorem curve_irreducibleSpace (hn : 0 < n) : IrreducibleSpace (fermatCurveScheme n) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced (fermatCurveScheme n)).mp
    (curve_isIntegral n hn) |>.1

/-- chart-0 开集非空（`Spec (R n)` 非空）。 -/
theorem chart0_opensRange_nonempty (hn : 0 < n) :
    Nonempty (fermatChart0ToCurve n).opensRange := by
  haveI : IsDomain (R n) := Mzk1G1A3ChartFracActual.chartRing_isDomain n hn
  haveI : Nonempty (PrimeSpectrum (R n)) := inferInstance
  obtain ⟨x⟩ := ‹Nonempty (PrimeSpectrum (R n))›
  exact ⟨(fermatChart0ToCurve n) x, ⟨x, rfl⟩⟩

section
variable [IrreducibleSpace (fermatCurveScheme n)]
variable [Nonempty (fermatChart0ToCurve n).opensRange]

/-- **F2.3 收口（chart-0）**：`R n` 的分数环是曲线的函数域。 -/
theorem isFractionRing_chart0_functionField (hn : 0 < n) :
    @IsFractionRing (R n) _ (fermatCurveScheme n).functionField _
      ((algebraMap Γ(fermatCurveScheme n, (fermatChart0ToCurve n).opensRange)
          (fermatCurveScheme n).functionField).comp
        (chart0_sections_ringEquiv n).symm.toRingHom).toAlgebra := by
  haveI : IsIntegral (fermatCurveScheme n) := curve_isIntegral n hn
  haveI : IsLocallyNoetherian (fermatCurveScheme n) := curve_locallyNoetherian n
  have hΓ : IsFractionRing Γ(fermatCurveScheme n, (fermatChart0ToCurve n).opensRange)
      (fermatCurveScheme n).functionField :=
    agFunctionField_isFractionRing_of_isAffineOpen _ (chart0_isAffineOpen n)
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
    (R := ↥Γ(fermatCurveScheme n, (fermatChart0ToCurve n).opensRange))
    (S := ↥(fermatCurveScheme n).functionField)
    (P := R n)
    (chart0_sections_ringEquiv n)).mp hΓ

end

#print axioms curve_locallyNoetherian
#print axioms curve_irreducibleSpace
#print axioms chart0_opensRange_nonempty
#print axioms isFractionRing_chart0_functionField

end LeanFormal.IUT.XiFPaper.Mzk1G1A3FunctionFieldFinalActual