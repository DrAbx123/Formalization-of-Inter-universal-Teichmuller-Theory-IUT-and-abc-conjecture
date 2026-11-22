import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.S927FinalWeightedInequalityActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S946QPilotCarrierAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S927FinalWeightedInequalityActual
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
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The model carrier on which s914R/s914S live. -/
abbrev QPilotModelCarrier : Type :=
  qVFamTensorBlock T b

/-- Exact paper-carrier bridge structure: an actual paper q-pilot carrier type
with a map to the model carrier, a q-pilot image, and the image-subset
inequality.  The actual paper object's component fields are the strip,
one-column structure, line bundle and Kummer arrow; this structure records
the missing assembly into a single carrier. -/
structure PaperQPilotCarrierBridge where
  Carrier : Type
  toModel : Carrier → QPilotModelCarrier (T := T) b
  qPilotImage : Set Carrier
  qPilotImage_subset_R : toModel '' qPilotImage ⊆ s914R (T := T) b
  carries_strip : Prop
  carries_oneColumn : Prop
  carries_lineBundle : Prop
  carries_kummer : Prop

/-- Exact carrier bridge obligation.  No inhabitant is asserted. -/
def S946PaperQPilotCarrierBridgeRequired : Prop :=
  Nonempty (PaperQPilotCarrierBridge (T := T) b)

/-- The paper q-pilot object's scalar field is a real number, not the model
region set. -/
theorem paperQPilotObject_scalar_carrier :
    (O.qPilotLogVolume : Real) = O.qPilotLogVolume :=
  rfl

/-- R and S are both subsets of the same qVFam model carrier; the S914/S924
comparison is same-carrier at the model level. -/
theorem model_R_S_same_carrier :
    s914R (T := T) b ⊆ s914S (T := T) b :=
  s914R_subset_S (T := T) b

/-- Exact audit conclusion: within the model carrier, R is contained in S. -/
def S946CarrierAudit : Prop :=
  s914R (T := T) b ⊆ s914S (T := T) b

theorem s946CarrierAudit_holds :
    S946CarrierAudit (T := T) b :=
  s914R_subset_S (T := T) b

/-- Exact paper carrier bridge obligation, recorded separately; no inhabitant. -/
def S946PaperCarrierBridgeGap : Prop :=
  S946PaperQPilotCarrierBridgeRequired (T := T) b

end LeanFormal.IUT.XiFPaper.S946QPilotCarrierAuditActual

end
