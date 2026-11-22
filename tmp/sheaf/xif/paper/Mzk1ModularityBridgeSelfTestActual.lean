import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# stepxi modularity bridge self-test (A781)

Self-contained arithmetic check of the bridge lemma. The production file
`Mzk1ModularityBridgeActual.lean` imports the real
`Mzk1FinalBoundarySzpiroActual.Szpiro6Shape`; this companion is computable now
and uses a local copy with the same definition. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ModularityBridgeSelfTestActual

def Szpiro6ShapeLocal (logq logdf C : Real) : Prop := logq ≤ 6 * logdf + C

def ModularityDegreeBound (logDelta logN C ε : Real) : Prop :=
  logDelta ≤ (2 + ε) * logN + C

theorem modularityDeltaBound_to_szpiro6
    (logDelta logN logq logdf C ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : 0 ≤ logN)
    (hδ : ModularityDegreeBound logDelta logN C ε)
    (hq : logq = 2 * logDelta) (hdf : logdf = logN) :
    Szpiro6ShapeLocal logq logdf (2 * C) := by
  unfold ModularityDegreeBound Szpiro6ShapeLocal at *
  rw [hq, hdf]
  nlinarith

end LeanFormal.IUT.XiFPaper.Mzk1ModularityBridgeSelfTestActual
