/- P8/G1 producer attempt: try to construct the all-epsilon Frey producer from
the actual G1 §13.1-13.3 compactness data; record the exact missing bridge. -/
import tmp.sheaf.xif.paper.Mzk1G1AllCompactActual
import tmp.sheaf.xif.paper.Mzk1G1CriterionAllActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ProducerAttempt
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual

def g1Compactness : Prop := UniformEpsilonCriterionRatAll belyiAllCompactSequence
theorem g1Compactness_actual : g1Compactness := belyiAllCompactSequence_uniformEpsilon

def belyiCompactnessToFreyHeight : Prop :=
  g1Compactness → (∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε))

theorem producer_of_bridge (h : belyiCompactnessToFreyHeight) :
    ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε) :=
  h g1Compactness_actual

theorem criterionAll_of_bridge (h : belyiCompactnessToFreyHeight) :
    ABCEllipticHeightCriterionAll := by
  classical
  exact criterionAll_of_freyHeight
    (fun ε hε => Classical.choice (producer_of_bridge h ε hε))

def firstMissingObject : String :=
  "belyiCompactnessToFreyHeight (Belyi compactness -> all-epsilon Frey height bound)"
def missingObjects : List String :=
  [ "belyiCompactnessToFreyHeight"
  , "FreyHeightBound epsilon producer (ABC-level height inequality)"
  ]
theorem missingObjects_length : missingObjects.length = 2 := rfl
#print axioms g1Compactness_actual
#print axioms criterionAll_of_bridge
end LeanFormal.IUT.XiFPaper.P8ProducerAttempt
end
