import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G2CDConsumerActual — G2.c/G2.d consumers (height bound + strength calibration)

DAG nodes: iutiv-abc:G2.c (heightWeightBound assembly) and iutiv-abc:G2.d (strength iff).
The core proofs are already in Cor312ToABCBridgeInterface.lean; this file records the
consumer-visible consequences used by the fragment and by the ABC height layer:

* Cor312ToABCBridgeInterface -> ABCHeightWeightAdditiveBoundV2 (G2.c consumer);
* Nonempty interface <-> ABCConjecture strength calibration (G2.d);
* the per-epsilon extraction API.

No new paper content; conditional theorems stay conditional on the interface inhabitant.
No closure claim; gate NOT PASSED. Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G2CDConsumerActual

open LeanFormal.IUT

/-- **G2.c consumer:** the bridge interface yields the version-2 additive height bound. -/
theorem ABCHeightWeightAdditiveBoundV2_of_bridgeInterface
    (D : Cor312ToABCBridgeInterface) : ABCHeightWeightAdditiveBoundV2 :=
  cor312ToABCBridge_heightBound D

/-- **G2.c per-epsilon extraction:** the explicit constant from the interface. -/
theorem exists_heightBound_constant_of_bridgeInterface
    (D : Cor312ToABCBridgeInterface) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  ABCHeightWeightAdditiveBoundV2.exists_constant
    (ABCHeightWeightAdditiveBoundV2_of_bridgeInterface D) hepsilon

/-- **G2.d strength calibration:** Nonempty bridge interface iff ABCConjecture. -/
theorem bridgeInterface_nonempty_iff_abcConjecture :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture

/-- **G2.d forward direction:** an inhabitant gives ABCConjecture. -/
theorem abcConjecture_of_bridgeInterface (D : Cor312ToABCBridgeInterface) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture D

/-- **G2.d backward direction:** ABCConjecture yields an inhabitant (strength calibration;
no proof of the interface's named gaps). -/
theorem bridgeInterface_nonempty_of_abcConjecture (h : ABCConjecture) :
    Nonempty Cor312ToABCBridgeInterface.{0} :=
  bridgeInterface_nonempty_iff_abcConjecture.mpr h

/-- Rows: G2.c/G2.d consumer status. -/
def g2ConsumerRows : List (String × String × String) :=
  [ ("G2.c heightWeightBound assembly", "cor312ToABCBridge_heightBound (core)", "PROVED (conditional on G2)"),
    ("G2.c additive bound consumer", "ABCHeightWeightAdditiveBoundV2_of_bridgeInterface", "PROVED"),
    ("G2.d strength iff", "bridgeInterface_nonempty_iff_abcConjecture", "PROVED"),
    ("G2.d forward/backward", "abcConjecture_of_bridgeInterface / bridgeInterface_nonempty_of_abcConjecture", "PROVED"),
    ("scope", "conditional on interface inhabitant; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g2ConsumerRows_length : g2ConsumerRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G2CDConsumerActual

end
