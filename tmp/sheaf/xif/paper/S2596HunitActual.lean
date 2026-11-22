import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.ABCBridge.Bridge.Cor312CarrierRealizationSpec

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2596HunitActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The frozen hunit comparison is satisfiable with the canonical constant
`D₀ = max D.degreeBound 0`, for every unit-region/Haar datum. -/
theorem S2596_hunit (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (D : I.SourceUnitRegionHaarData v R n) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion <=
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).hull +
        ENNReal.ofReal (max D.degreeBound 0) :=
  I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume
    v R n D (D₀ := max D.degreeBound 0) (le_max_right _ _) (by
      calc ENNReal.ofReal D.degreeBound
          ≤ ENNReal.ofReal (max D.degreeBound 0) :=
            ENNReal.ofReal_le_ofReal (le_max_left _ _)
        _ ≤ I.sourceHullVolume v R n + ENNReal.ofReal (max D.degreeBound 0) := by
            simpa only [zero_add] using
              add_le_add zero_le (le_refl (ENNReal.ofReal (max D.degreeBound 0))))

#check S2596_hunit
#print axioms S2596_hunit

end LeanFormal.IUT.XiFPaper.S2596HunitActual
end