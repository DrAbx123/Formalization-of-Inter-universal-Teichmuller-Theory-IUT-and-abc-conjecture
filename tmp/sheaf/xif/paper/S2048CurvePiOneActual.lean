import tmp.sheaf.xif.paper.S2038PaperOActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2048CurvePiOneActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2038PaperOActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual (PaperV)
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open AlgebraicGeometry

/-- Exact missing data of S2038 CurvePiOneData, excluding the actual curve
curveScheme Q_[v.1] and its rfl equality.  No inhabitant is asserted. -/
structure S2048CurvePiOneMissing (v : PaperV) where
  card : CurveEtaleFundamentalGroupCard ℚ_[v.1]
  tempered : Type
  [groupTempered : Group tempered]
  [topTempered : TopologicalSpace tempered]
  comparison : tempered →* (card.fundamentalGroup : Type)
  proj : tempered →* @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  proj_surjective : Function.Surjective proj
  geometric_nontrivial : Nontrivial proj.ker

/-- Exact first missing family: actual curve pi1 data at every paper place. -/
structure S2048CurvePiOneFamily where
  data : (v : PaperV) → S2048CurvePiOneMissing v

/-- The card alone is a frozen source obligation. -/
def S2048CurveEtaleCardRequired (v : PaperV) : Prop :=
  Nonempty (CurveEtaleFundamentalGroupCard ℚ_[v.1])

end LeanFormal.IUT.XiFPaper.S2048CurvePiOneActual
end