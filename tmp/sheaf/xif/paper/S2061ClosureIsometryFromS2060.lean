import tmp.sheaf.xif.paper.S2056IsometricClosureActual
import tmp.sheaf.xif.paper.S2057NormBridgeFromIsometry
import tmp.sheaf.xif.paper.S2060CompletionUnitsActual
import tmp.sheaf.xif.paper.S2038PaperOActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
open LeanFormal.IUT.XiFPaper.S2057NormBridgeFromIsometry
open LeanFormal.IUT.XiFPaper.S2060CompletionUnitsActual
namespace LeanFormal.IUT.XiFPaper.S2061ClosureIsometryFromS2060
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- S2060's actual norm-preserving Q_p-algebra equivalence gives the
S2056ClosureIsometry at the bad completion place. -/
noncomputable def S2061ClosureIsometry :
    S2056ClosureIsometry (qVPlace (l := l) T b) where
  equiv := (s2060AlgClosureEquiv T b).toRingEquiv
  norm_pres := s2060AlgClosureEquiv_norm T b
noncomputable def S2061IntegralUnitsEquiv :
    S2055CompletionIntegralUnits (qVPlace (l := l) T b) ≃*
      S2055QpIntegralUnits (qVPlace (l := l) T b) :=
  S2056IntegralUnitsEquiv (qVPlace (l := l) T b) (S2061ClosureIsometry T b)
#check S2061ClosureIsometry
#check S2061IntegralUnitsEquiv
end LeanFormal.IUT.XiFPaper.S2061ClosureIsometryFromS2060
end
