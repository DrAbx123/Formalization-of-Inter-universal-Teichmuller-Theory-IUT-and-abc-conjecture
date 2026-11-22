import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-!
# ShehddInterfaceFormConsumerActualAdapted — Cor312ToABCBridgeInterface => ABC forms

STEP 0 prior-art (reuse only):
* ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:
  cor312ToABCBridge_abcConjecture (D : Cor312ToABCBridgeInterface) : ABCConjecture;
* ABCBridge/Bridge/IUTToABC.lean: abcConjecture_iff_abcLogConjecture;
* ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.

This file exposes the two equivalent ABC forms (log and additive height-weight) directly
from a Cor312ToABCBridgeInterface, i.e. the paper-route interface implies every retained
equivalent shape.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInterfaceFormConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED composition:** a Cor 3.12 -> ABC bridge interface yields ABC in log form. -/
theorem abcLogConjecture_of_interface (D : Cor312ToABCBridgeInterface) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (cor312ToABCBridge_abcConjecture D)

/-- **PROVED composition:** a Cor 3.12 -> ABC bridge interface yields the additive
height-weight form. -/
theorem abcHeightWeightAdditive_of_interface (D : Cor312ToABCBridgeInterface) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (cor312ToABCBridge_abcConjecture D)

/-- **PROVED composition:** the interface's height bound is equivalent to the additive
form (both are ABC under the proved equivalences). -/
theorem interface_heightBound_and_additive (D : Cor312ToABCBridgeInterface) :
    (∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A) ∧
      ABCHeightWeightAdditiveBoundV2 :=
  ⟨cor312ToABCBridge_heightBound D,
    abcHeightWeightAdditive_of_interface D⟩

/-- Row record: reused interface/equivalence theorems vs composed consumer forms. -/
def interfaceFormRows : List (String × String × String) :=
  [ ("interface => ABCConjecture", "REUSED PROVED", "cor312ToABCBridge_abcConjecture")
  , ("interface => height bound (per epsilon additive constant)", "REUSED PROVED", "cor312ToABCBridge_heightBound")
  , ("ABC <-> log form", "REUSED PROVED", "abcConjecture_iff_abcLogConjecture")
  , ("ABC <-> additive form", "REUSED PROVED", "abcConjecture_iff_ABCHeightWeightAdditiveBoundV2")
  , ("interface => log form", "COMPOSED PROVED", "abcLogConjecture_of_interface")
  , ("interface => additive form", "COMPOSED PROVED", "abcHeightWeightAdditive_of_interface")
  , ("interface => height bound AND additive form", "COMPOSED PROVED", "interface_heightBound_and_additive") ]

theorem interfaceFormRows_length : interfaceFormRows.length = 7 := rfl

#check abcLogConjecture_of_interface
#check abcHeightWeightAdditive_of_interface
#check interface_heightBound_and_additive
#check interfaceFormRows_length

end LeanFormal.IUT.XiFPaper.ShehddInterfaceFormConsumerActualAdapted
end
