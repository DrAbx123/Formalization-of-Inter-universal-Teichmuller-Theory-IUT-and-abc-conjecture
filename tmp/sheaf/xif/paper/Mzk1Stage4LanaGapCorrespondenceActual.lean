import tmp.sheaf.xif.paper.Mzk1Stage4LanaIutIVEstimateActual
import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual

/-! # Mzk1Stage4LanaGapCorrespondenceActual (stage4 lane; gap correspondence)

A630 module: explicit correspondence table between the LANA IUT IV estimate stages and
the two ABC comparison gaps used by the stage4 chain (Gap 1: height/region volume;
Gap 2: region volume/weight).  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaGapCorrespondenceActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaIutIVEstimateActual

universe u

/-- A correspondence entry: LANA source, its fields, and the ABC gap it supplies. -/
structure GapCorrespondence where
  /-- the LANA source file (relative path). -/
  source : String
  /-- the LANA field/structure involved. -/
  field : String
  /-- the ABC gap supplied. -/
  gap : String

/-- The correspondence entries used by the stage4 consumer. -/
def gapCorrespondenceTable : List GapCorrespondence :=
  [ { source := "tmp/sheaf/lana_latest/Iut/Concrete/LocalEstimate.lean"
      field := "localEstimate.packetVol_mono"
      gap := "region-volume monotonicity" }
  , { source := "tmp/sheaf/lana_latest/Iut/Concrete/LocalEstimate.lean"
      field := "localEstimate.vol_finite"
      gap := "local volume finiteness" }
  , { source := "tmp/sheaf/lana_latest/Iut/Implication/Theorem110.lean"
      field := "theorem110"
      gap := "Gap 1 + Gap 2 (height/region-volume; region-volume/weight)" }
  ]

/-- The correspondence table has three entries. -/
theorem gapCorrespondenceTable_length : gapCorrespondenceTable.length = 3 := rfl

/-- LANA local-estimate region volumes give the Gap 1 shape, restated through the
abstract Gap1 structure. -/
theorem gap1_via_gapStructure {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (a b c : Nat) :
    Gap1 (E.height a b c) ((1 + ε) * E.vol (E.region a b c)) where
  bound := E.height_le_region ε hε a b c

/-- LANA local-estimate region volumes give the Gap 2 shape, restated through the
abstract Gap2 structure. -/
theorem gap2_via_gapStructure {α : Type u} (E : LanaLocalEstimate α)
    (ε : Real) (hε : 0 < ε) (D : Real)
    (hD : ∀ a b c : Nat, E.vol (E.region a b c) ≤
      (1 + ε) * E.weight a b c + E.thetaBound + D) (a b c : Nat) :
    Gap2 (E.vol (E.region a b c)) (E.weight a b c) E.thetaBound D ε where
  bound := hD a b c

#check GapCorrespondence
#check gapCorrespondenceTable
#check gapCorrespondenceTable_length
#check gap1_via_gapStructure
#check gap2_via_gapStructure

end LeanFormal.IUT.XiFPaper.Mzk1Stage4LanaGapCorrespondenceActual
end
