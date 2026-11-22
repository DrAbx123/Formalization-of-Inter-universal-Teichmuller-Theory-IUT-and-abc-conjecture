import tmp.sheaf.xif.paper.S2760MixedSpacePaperFactorActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open scoped nonZeroDivisors Classical
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2761BridgeHullDataCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The partial bridge data filled by S2760: carrier and hullData. -/
structure S2761BridgeHullPart where
  carrier : Type u
  hullData : IQHullLogVolumeInterface carrier

/-- S2760 supplies the mixed-space carrier and the actual paper-factor hull
interface. -/
noncomputable def S2761BridgeHullPartOf
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    S2761BridgeHullPart where
  carrier := NumberField.mixedEmbedding.mixedSpace K
  hullData := S2760IQHullInterface K J

/-- The carrier/hullData fields are exactly S2760's mixed-space interface. -/
theorem S2761_hullData_eq
    (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ) :
    (S2761BridgeHullPartOf K J).hullData =
      S2760IQHullInterface K J := rfl

/-- Exact missing data for the full `Cor312ToABCBridgeInterface`: the
per-epsilon comparison region and a point map from ABC triples into the
mixed-space carrier.  No point map or epsilon comparison is produced here. -/
structure S2761BridgeEpsilonGap where
  logShellPoint : Nat → Nat → Nat →
    NumberField.mixedEmbedding.mixedSpace K
  epsilonComparison :
    ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison
        (S2760IQHullInterface K
          (1 : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)) epsilon

#check S2761BridgeHullPart
#check S2761BridgeHullPartOf
#check S2761_hullData_eq
#check S2761BridgeEpsilonGap
#print axioms S2761_hullData_eq

end LeanFormal.IUT.XiFPaper.S2761BridgeHullDataCarrierActual
end
