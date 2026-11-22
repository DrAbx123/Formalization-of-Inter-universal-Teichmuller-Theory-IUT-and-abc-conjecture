import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi modularity bridge (ROUTES §10 route alpha)

Pure-real bridge from the modular parameterization degree bound
`log delta_{N,1} <= (2+eps) * log N + C` to `Szpiro6Shape`.

WARNING: the arithmetic identification of `logq`, `logdf` with
`2*log delta`, `log N` is an explicit hypothesis here; it is NOT proved. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ModularityBridgeActual

open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual

/-- Route-alpha modular degree bound (paper-side target, real form). -/
def ModularityDegreeBound (logDelta logN C ε : Real) : Prop :=
  logDelta ≤ (2 + ε) * logN + C

/-- Bridge lemma: under the Frey-curve identifications `logq = 2 log delta`,
`logdf = log N`, and `0 <= eps <= 1`, the modular parameterization degree bound
implies `Szpiro6Shape logq logdf (2*C)`.

The constants are explicit: `6 = 2*(2+eps)|_{eps=1+...}`; the factor `2` comes
from `logq = 2 log delta`. -/
theorem modularityDeltaBound_to_szpiro6
    (logDelta logN logq logdf C ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : 0 ≤ logN)
    (hδ : ModularityDegreeBound logDelta logN C ε)
    (hq : logq = 2 * logDelta) (hdf : logdf = logN) :
    Szpiro6Shape logq logdf (2 * C) := by
  unfold ModularityDegreeBound Szpiro6Shape at *
  rw [hq, hdf]
  nlinarith

/-- The same bridge with a named constant `C' = 2*C`. -/
theorem modularityDeltaBound_to_szpiro6'
    (logDelta logN logq logdf C ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : 0 ≤ logN)
    (hδ : ModularityDegreeBound logDelta logN C ε)
    (hq : logq = 2 * logDelta) (hdf : logdf = logN) :
    ∃ C' : Real, Szpiro6Shape logq logdf C' :=
  ⟨2 * C, modularityDeltaBound_to_szpiro6 logDelta logN logq logdf C ε
    hε0 hε1 hN hδ hq hdf⟩

end LeanFormal.IUT.XiFPaper.Mzk1ModularityBridgeActual

end
