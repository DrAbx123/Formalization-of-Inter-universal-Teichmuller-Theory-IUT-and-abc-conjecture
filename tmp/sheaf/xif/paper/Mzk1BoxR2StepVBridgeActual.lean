import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic
/-!
# R2 StepV bridge: paper hull bound vs `collectionChoiceBound`

`FinitePlaceStepVAssembly.arithmeticTuple_stepV_hull_normalizedLogVolume_le_paperBound`
(line 814) gives
`V := arithmeticTupleNormalizedLogVolume … hull ≤ (-λ + ∑ d_i + 1) log p
   + ∑_{i∈exceptional} (3 + log e_i)`.
`StepVProcessionAverage.collectionChoiceBound` uses
`(-(j²/(2l)) oq(et idag) + ∑ d(et i) + 1) log p + 4(j+1) iotaL`.
The paper R2 box inequality `V ≤ collectionChoiceBound` therefore needs the parameter
identification `λ = (j²/(2l)) oq(et idag)` and
`∑_{i∈exceptional}(3+log e_i) = 4(j+1) iotaL`, and the same `d` — recorded here as an
explicit hypothesis (`hparam`); absent from the current tree as a proved equality.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2StepVBridgeActual

/-- Bridge from the paper StepV hull bound to `collectionChoiceBound`, given the exact
parameter equality `hparam` (the missing paper-to-Section-1 identification). -/
theorem stepV_hull_le_collectionChoiceBound
    (V paperBound choice : ℝ) (hV : V ≤ paperBound) (hparam : paperBound = choice) :
    V ≤ choice :=
  le_trans hV hparam.le

#print axioms stepV_hull_le_collectionChoiceBound
end LeanFormal.IUT.XiFPaper.Mzk1BoxR2StepVBridgeActual
end