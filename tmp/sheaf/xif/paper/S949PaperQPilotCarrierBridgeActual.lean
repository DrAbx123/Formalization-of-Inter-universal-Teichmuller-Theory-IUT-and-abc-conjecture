import tmp.sheaf.xif.paper.S946QPilotCarrierAuditActual
import tmp.sheaf.xif.PaperQPilotObject

/-! # S949: paper qPilot carrier bridge from actual PaperQPilotObject components

The actual PaperQPilotObject supplies strip, oneColumn, lineBundle and
logKummer.  The missing assembly is a paper carrier type with a map to the
qVFam model and an image subset of R.  We record exactly that assembly; given
it, the S946 bridge is constructed with the actual components as its
carries_* propositions.  No fake carrier is chosen. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S949PaperQPilotCarrierBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S946QPilotCarrierAuditActual
open MeasureTheory

universe ua uv upi umon ui uG uX
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uX} {Choice : Type uX} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable (O : PaperQPilotObject (l := l) (V := V)
  (Label := Label) (Choice := Choice) I G envStrip)
variable {l0 : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l0)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing assembly: paper carrier, map to the qVFam model, image in R. -/
structure PaperCarrierAssembly where
  Carrier : Type
  toModel : Carrier → QPilotModelCarrier (T := T) b
  qPilotImage : Set Carrier
  qPilotImage_subset_R : toModel '' qPilotImage ⊆ s914R (T := T) b

/-- Build the S946 bridge from the assembly and actual PaperQPilotObject components. -/
noncomputable def bridgeOfAssembly (A : PaperCarrierAssembly (T := T) b) :
    PaperQPilotCarrierBridge (T := T) b where
  Carrier := A.Carrier
  toModel := A.toModel
  qPilotImage := A.qPilotImage
  qPilotImage_subset_R := A.qPilotImage_subset_R
  carries_strip := Nonempty (FPrimeStrip.{umon, uv, upi} V)
  carries_oneColumn := Nonempty (SourceOneColumnArithmeticHolomorphicStructure V)
  carries_lineBundle :=
    Nonempty (PaperLineBundleCarrierActual.PaperLineBundleCarrier
      (k := I.initial.arithmetic.Fmod))
  carries_kummer := Nonempty (SourceKummerArrow G envStrip O.strip)

/-- The bridge carries the actual strip/one-column/line-bundle/Kummer components. -/
theorem bridgeOfAssembly_components
    (A : PaperCarrierAssembly (T := T) b) :
    (bridgeOfAssembly (O := O) (T := T) (b := b) A).carries_strip ∧
      (bridgeOfAssembly (O := O) (T := T) (b := b) A).carries_oneColumn ∧
      (bridgeOfAssembly (O := O) (T := T) (b := b) A).carries_lineBundle ∧
      (bridgeOfAssembly (O := O) (T := T) (b := b) A).carries_kummer :=
  ⟨⟨O.strip⟩, ⟨O.oneColumn⟩, ⟨O.lineBundle⟩, ⟨O.logKummer⟩⟩

/-- Exact minimal missing input: paper-carrier assembly. -/
def S949PaperCarrierAssemblyRequired : Prop :=
  Nonempty (PaperCarrierAssembly (T := T) b)

end LeanFormal.IUT.XiFPaper.S949PaperQPilotCarrierBridgeActual
end
