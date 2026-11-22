import tmp.sheaf.xif.paper.S2040PaperOUnitsMuAmbientActual
import tmp.sheaf.xif.paper.S2055CompletionIntegralUnitsActual
import tmp.sheaf.xif.paper.S2046CompletionOUnitsActual

/-! # S2040 completion-level paper O^× carrier from S2055 integral units

Replaces the all-units S2035 carrier by S2055's actual completion integral units
`(Integers (SourceAlgebraicClosure place))^×` and its O^×μ quotient.  The actual
carrier fills the paper O^×/O^×μ slots; the identification to the S1978 Q_p
integral units and the qVPlace completion bridge remain exact missing. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040CompletionBridgeS2055Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S2055CompletionIntegralUnitsActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

/-- The actual completion integral-units carrier of S2055 fills the paper
O^×/O^×μ carrier slots.  No Q_p-model identification is assumed. -/
noncomputable def s2040PaperOUnitsMuAmbientOfS2055
    (place : NumberField.FinitePlace ℚ) :
    S2040PaperOUnitsMuAmbient where
  OUnits := S2055CompletionIntegralUnits place
  OUnitsMu := S2055CompletionOUnitsMu place
  ambientValues := S2055CompletionIntegralUnits place
  quotient_compatible := Nonempty (S2055CompletionOUnitsMu place)
  ambient_values_paper := Nonempty (S2055CompletionIntegralUnits place)
  OUnits_nontrivial := Nonempty (S2055CompletionIntegralUnits place)

/-- Exact missing S2055 integral-units identification, at a rational place. -/
abbrev S2040S2055IntegralUnitsMissing
    (place : NumberField.FinitePlace ℚ) : Type :=
  S2055IntegralUnitsIdentificationRequired place

/-- Exact missing bridge from the root-stack completion at `qVPlace T b` to the
canonical S2055/S2046 completion integral-units carrier.  The norm bridge is the
canonical S2046NormBridge, not a duplicate.  No inhabitant is asserted. -/
structure S2040CompletionBridgeRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  v : FinitePrimePlace 2 7
  qVCompletionEquiv :
    Completion (qVPlace (l := l) T b) ≃+* Completion (QPlace v)
  qVIntegralUnitsEquiv :
    (Integers (AlgebraicClosure (Completion (qVPlace (l := l) T b))))ˣ ≃*
      S2055CompletionIntegralUnits (QPlace v)
  normBridge : S2046NormBridge v

/-- A completion bridge supplies the paper carrier at the rational place. -/
noncomputable def s2040PaperOUnitsMuAmbientOfBridge
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (B : S2040CompletionBridgeRequired T b) :
    S2040PaperOUnitsMuAmbient :=
  s2040PaperOUnitsMuAmbientOfS2055 (QPlace B.v)

#check s2040PaperOUnitsMuAmbientOfS2055
#check S2040S2055IntegralUnitsMissing
#check S2040CompletionBridgeRequired
#check s2040PaperOUnitsMuAmbientOfBridge

end LeanFormal.IUT.XiFPaper.S2040CompletionBridgeS2055Actual
end
