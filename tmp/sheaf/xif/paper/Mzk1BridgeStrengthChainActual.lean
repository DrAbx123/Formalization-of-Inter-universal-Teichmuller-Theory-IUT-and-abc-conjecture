import LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface
import LeanFormal/IUT/ABCBridge/Bridge/IUTToABC
import LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1BridgeStrengthChainActual — A479 real equivalence chain (Cor312 bridge strength)

New equivalence results chaining the bridge-strength calibration
(`Cor312ToABCBridgeInterface.lean:605`:
`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`) with the accepted ABC
form equivalences (`IUTToABC.lean:36` log form, :64 height form;
`ABCHeightArithmeticWeightComparison.lean:167` v2 additive-bound form):

1. `bridge_nonempty_iff_log`: inhabiting the interface is equivalent to the ABC
   log conjecture;
2. `bridge_nonempty_iff_weightHeight`: inhabiting the interface is equivalent
   to the height/weight additive bound v2;
3. `bridge_strength_package`: the two equivalences together.

These are new transitive compositions (not donor aliases).

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1BridgeStrengthChainActual

open LeanFormal.IUT

/-- Interface inhabitation ↔ ABC log conjecture (chain of :605 with :36). -/
theorem bridge_nonempty_iff_log :
    Nonempty Cor312ToABCBridgeInterface ↔ ABCLogConjecture :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.trans
    abcConjecture_iff_abcLogConjecture

/-- Interface inhabitation ↔ height/weight additive bound v2 (chain of :605
with :64/:167). -/
theorem bridge_nonempty_iff_weightHeight :
    Nonempty Cor312ToABCBridgeInterface ↔ ABCHeightWeightAdditiveBoundV2 :=
  cor312ToABCBridgeInterface_nonempty_iff_abcConjecture.trans
    (abcConjecture_iff_abcArithmeticWeightHeightBound.trans
      abcConjecture_iff_ABCHeightWeightAdditiveBoundV2)

/-- Joint bridge-strength package. -/
theorem bridge_strength_package :
    (Nonempty Cor312ToABCBridgeInterface ↔ ABCLogConjecture) ∧
      (Nonempty Cor312ToABCBridgeInterface ↔ ABCHeightWeightAdditiveBoundV2) :=
  ⟨bridge_nonempty_iff_log, bridge_nonempty_iff_weightHeight⟩

#check bridge_nonempty_iff_weightHeight
#check bridge_strength_package

end LeanFormal.IUT.XiFPaper.Mzk1BridgeStrengthChainActual
end