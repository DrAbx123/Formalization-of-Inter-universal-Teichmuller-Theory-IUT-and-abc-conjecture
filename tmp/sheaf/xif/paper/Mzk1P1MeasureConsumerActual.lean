import tmp.sheaf.xif.paper.Mzk1P1MeasureTransferStatementsActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1P1MeasureConsumerActual — P1 measure-transfer statement bundle

Reuses the EXIT0 P1 measure-transfer statement definitions (max-degree non-increase,
strict measure decrease, finite max-degree non-increase) as a bundle with
projections.  No measure statement is proved; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureConsumerActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureTransferStatementsActual

structure P1MeasureBundle : Prop where
  maxDegNonIncrease : P1MaxDegNonIncrease
  strictDecrease : P1MeasureStrictDecrease
  finiteNonIncrease : FiniteMaxDegNonIncrease

theorem p1MeasureBundle_maxDeg (B : P1MeasureBundle) : P1MaxDegNonIncrease :=
  B.maxDegNonIncrease

theorem p1MeasureBundle_strict (B : P1MeasureBundle) : P1MeasureStrictDecrease :=
  B.strictDecrease

theorem p1MeasureBundle_finite (B : P1MeasureBundle) : FiniteMaxDegNonIncrease :=
  B.finiteNonIncrease

def p1MeasureConsumerRows : List (String × String × String) :=
  [ ("bundle", "P1MeasureBundle", "DEF (reuses EXIT0 statements)"),
    ("projections", "p1MeasureBundle_maxDeg/strict/finite", "PROVED"),
    ("scope", "statements only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem p1MeasureConsumerRows_length : p1MeasureConsumerRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureConsumerActual

end
