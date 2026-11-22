import tmp.sheaf.xif.paper.S2040PaperOUnitsMuAmbientActual
import tmp.sheaf.xif.paper.S2060CompletionUnitsActual
import tmp.sheaf.xif.paper.S2065IsometricClosureActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual
open LeanFormal.IUT.XiFPaper.S2060CompletionUnitsActual
open LeanFormal.IUT.XiFPaper.S2065IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
namespace LeanFormal.IUT.XiFPaper.S2066PaperOUnitsMuUnconditionalAdapted
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- The S2060 actual qVPlace completion identification fills the S2040
carrier-corrected structure. -/
noncomputable def S2066CompletionLocalIdentification :
    S2040CompletionLocalIdentification (l := l) T b where
  p := s2060Prime T b
  hprime := completionRationalPrime_fact (qVPlace (l := l) T b)
  completionUnitEquiv := s2060CompletionIntegralUnitsEquiv T b
  norm_compatible := s2060CompletionIntegralUnitsEquiv_val_norm T b
/-- The S2040 paper O^/O^mu/ambient package is now unconditional at qVPlace. -/
noncomputable def S2066PaperOUnitsMuAmbient :
    S2040PaperOUnitsMuAmbient :=
  s2040PaperOUnitsMuAmbientOfCompletion T b (S2066CompletionLocalIdentification T b)
/-- The S2046 canonical norm bridge at every one-column place, unconditional. -/
noncomputable def S2066NormBridge (v : FinitePrimePlace 2 7) :
    S2046NormBridge v :=
  S2065NormBridgeOf v
theorem S2066NormBridge_nonempty (v : FinitePrimePlace 2 7) :
    Nonempty (S2046NormBridge v) :=
  ⟨S2066NormBridge v⟩
#check S2066CompletionLocalIdentification
#check S2066PaperOUnitsMuAmbient
#check S2066NormBridge
#check S2066NormBridge_nonempty
end LeanFormal.IUT.XiFPaper.S2066PaperOUnitsMuUnconditionalAdapted
end
