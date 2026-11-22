/- G1 height-producer attempt: try to build the actual all-epsilon Frey height
producer from the G1 §13.1-13.3 compactness/uniform-epsilon data (not as an
input hypothesis).  The compactness data is actual; the missing object is the
bridge from Belyi compactness to the arithmetic Frey height bound. -/
import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1HeightProducerAttemptActual

open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- G1 §13.1-13.3 actual compactness/uniform-epsilon data. -/
def G1CompactnessData : Prop := UniformEpsilonCriterionRatAll belyiAllCompactSequence

theorem g1CompactnessData_actual : G1CompactnessData :=
  belyiAllCompactSequence_uniformEpsilon

/-- The exact missing §13.1-13.3 object: a bridge from the actual Belyi
compactness data to the all-epsilon Frey height bound. -/
def BelyiCompactnessToFreyHeight : Prop :=
  G1CompactnessData → (∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε))

/-- Attempt: from the missing bridge the actual all-epsilon producer follows. -/
theorem g1FreyProducer_of_bridge (h : BelyiCompactnessToFreyHeight) :
    ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε) :=
  h g1CompactnessData_actual

theorem g1CriterionAll_of_bridge (h : BelyiCompactnessToFreyHeight) :
    ABCEllipticHeightCriterionAll := by
  classical
  exact criterionAll_of_freyHeight
    (fun ε hε => Classical.choice (g1FreyProducer_of_bridge h ε hε))

/-- Exact first missing object (no declaration in the tree relates the G1
compactness/uniform-epsilon criterion to `FreyHeightBound`). -/
def firstMissingObject : String :=
  "BelyiCompactnessToFreyHeight: no declaration relates UniformEpsilonCriterionRatAll belyiAllCompactSequence to FreyHeightBound"

def missingObjects : List String :=
  [ "BelyiCompactnessToFreyHeight (compactness -> Frey height bridge)"
  , "actual FreyHeightBound epsilon producer (ABC-level height inequality)"
  ]

theorem missingObjects_length : missingObjects.length = 2 := rfl

#print axioms g1CompactnessData_actual
#print axioms g1FreyProducer_of_bridge
#print axioms g1CriterionAll_of_bridge

end LeanFormal.IUT.XiFPaper.Mzk1G1HeightProducerAttemptActual
end
