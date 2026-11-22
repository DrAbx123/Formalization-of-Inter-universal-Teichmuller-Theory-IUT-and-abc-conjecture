import tmp.sheaf.xif.paper.Node09TateZeroCountActual
import LeanFormal.IUT.Foundations.Geometry.TateCoordinatePeriodicity

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateYInversionActual

universe u
variable {K : Type u} [NormedField K]

/-- The honest twisted inversion law for the Y coordinate (existing donor). -/
theorem tateWeierstrassY_inv (q u : K) :
    TateCurve.tateWeierstrassY q u⁻¹ =
      -(u⁻¹) * TateCurve.yCoordinateSeriesTwisted q u := by
  rw [TateCurve.tateWeierstrassY, TateCurve.yCoordinateSeries_inv]

/-- Y branch selection residual: after X(u)=X(v) gives v=u or v=u^{-1} modulo q^Z,
the Y coordinate decides which branch.  The exact missing data is the comparison
Y(u)=Y(v) against the twisted inversion law. -/
def TateYBranchSelectionResidual (q : K) : Prop :=
  ∀ u v : K, u ≠ 0 →
    TateCurve.tateWeierstrassX q u = TateCurve.tateWeierstrassX q v →
      TateCurve.tateWeierstrassY q u = TateCurve.tateWeierstrassY q v →
        (∃ m : ℤ, q ^ m * u = v) ∨ (∃ m : ℤ, q ^ m * u⁻¹ = v)

def Node09TateYInversionStatus : List String :=
  [ "actual: Y inversion law yCoordinateSeries_inv expresses Y(q,u^{-1}) via the twisted series -(u^{-1})*yCoordinateSeriesTwisted",
    "TateYBranchSelectionResidual records the exact remaining branch-selection statement; no proof currently exists",
    "missing: comparison of Y(u) and Y(v) on the two X branches using the twisted inversion law and q-periodicity; needs the actual q-Laurent expansion of Y (only norm bounds exist)",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateYInversionActual