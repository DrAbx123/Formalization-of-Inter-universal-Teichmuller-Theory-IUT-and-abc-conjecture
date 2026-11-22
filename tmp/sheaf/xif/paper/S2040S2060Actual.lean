import tmp.sheaf.xif.paper.S2060CompletionUnitsActual
import tmp.sheaf.xif.paper.S2065IsometricClosureActual
import tmp.sheaf.xif.paper.S2040CompletionLayersActual
import tmp.sheaf.xif.paper.S2040CompletionBridgeS2055Actual
import tmp.sheaf.xif.paper.S2040NormBridgeS2056Actual

/-! # S2040: actual paper O^×/O^×μ from S2060 and unconditional layer (3) from S2065

Connects the carrier-corrected S2040 completion identification to S2060's actual
qVPlace integral-units bridge, and uses S2065's unconditional closure isometry for
the S2046 norm bridge.  No all-units carrier is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040S2060Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual
open LeanFormal.IUT.XiFPaper.S2060CompletionUnitsActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2065IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S2040CompletionLayersActual
open LeanFormal.IUT.XiFPaper.S2040CompletionBridgeS2055Actual
open LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

/-- S2060's carrier-corrected identification is an inhabitant of the S2040
integral-units identification. -/
noncomputable def s2040CompletionLocalIdentificationOfS2060
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (I : S2060CompletionLocalIdentification T b) :
    S2040CompletionLocalIdentification T b where
  p := I.p
  hprime := I.hprime
  completionUnitEquiv := I.completionUnitEquiv
  norm_compatible := I.norm_compatible

/-- The actual S2040 completion identification, without the all-units carrier. -/
noncomputable def s2040CompletionLocalIdentificationActual
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    S2040CompletionLocalIdentification T b :=
  s2040CompletionLocalIdentificationOfS2060 T b
    (s2060CompletionLocalIdentification T b)

/-- The actual paper O^×/O^×μ/ambient package from S2060's integral-units bridge. -/
noncomputable def s2040PaperOUnitsMuAmbientActual
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    S2040PaperOUnitsMuAmbient :=
  s2040PaperOUnitsMuAmbientOfCompletion T b
    (s2040CompletionLocalIdentificationActual T b)

/-- S2065's unconditional closure isometry gives the canonical S2046 norm bridge. -/
noncomputable def s2040NormBridgeUnconditional
    (v : FinitePrimePlace 2 7) : S2046NormBridge v :=
  S2065NormBridgeOf v

/-- With split data (1) and integral-units bridge (2), the full completion bridge
now uses the unconditional S2065 norm bridge. -/
noncomputable def s2040CompletionBridgeOfSplitUnconditional
    {T : SourceNativeInitialThetaData.{0} l}
    {b : Bad (nativePlaceSelection T)}
    (S : S2040QVPlaceSplitData T b)
    (U : S2040QVIntegralUnitsBridgeRequired T b S.v) :
    S2040CompletionBridgeRequired T b :=
  S2040CompletionBridgeOfLayers
    { v := S.v, completionEquiv := S.completionEquiv }
    { unitsEquiv := U.integralUnitsEquiv }
    (s2040NormBridgeUnconditional S.v)

#check s2040CompletionLocalIdentificationActual
#check s2040PaperOUnitsMuAmbientActual
#check s2040NormBridgeUnconditional
#check s2040CompletionBridgeOfSplitUnconditional

end LeanFormal.IUT.XiFPaper.S2040S2060Actual
end
