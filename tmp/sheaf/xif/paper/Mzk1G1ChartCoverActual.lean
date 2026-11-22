import tmp.sheaf.xif.paper.Mzk1G1FermatTwoChartGluingActual
import Mathlib.Tactic

/-!
# The two-chart Zariski cover of the glued Fermat curve (Lead lane, G-A (h) support)

Bool-indexed family of the two affine charts, shown to be an open cover; this is a
basic input for the geometric integrality/connectedness step (route §2.4 (h)).

No sorry, no axiom.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1G1ChartCoverActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual

/-- The two chart open subschemes of the glued Fermat curve. -/
def chartOpenFamily (n : Nat) : Bool → (fermatCurveScheme n).Opens :=
  fun b => if b then (fermatChartInfToCurve n).opensRange
    else (fermatChart0ToCurve n).opensRange

theorem chartOpenFamily_false (n : Nat) :
    chartOpenFamily n false = (fermatChart0ToCurve n).opensRange := rfl

theorem chartOpenFamily_true (n : Nat) :
    chartOpenFamily n true = (fermatChartInfToCurve n).opensRange := rfl

/-- The two affine charts cover the glued curve. -/
theorem chartOpenFamily_iSup_eq_top (n : Nat) :
    iSup (chartOpenFamily n) = ⊤ := by
  ext x
  change x ∈ iSup (chartOpenFamily n) ↔ x ∈ (⊤ : (fermatCurveScheme n).Opens)
  rw [TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    trivial
  · intro _
    obtain ⟨i, y, hy⟩ := (fermatTwoChartGlueData n).ι_jointly_surjective x
    obtain ⟨b⟩ := i
    cases b
    · refine ⟨false, ?_⟩
      show x ∈ (fermatChart0ToCurve n).opensRange
      exact ⟨y, hy⟩
    · refine ⟨true, ?_⟩
      show x ∈ (fermatChartInfToCurve n).opensRange
      exact ⟨y, hy⟩

#print axioms chartOpenFamily_iSup_eq_top

end LeanFormal.IUT.XiFPaper.Mzk1G1ChartCoverActual
end
