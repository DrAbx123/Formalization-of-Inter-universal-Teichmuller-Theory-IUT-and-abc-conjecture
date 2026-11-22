import tmp.sheaf.xif.paper.S1152FPrimeStripBridgeAuditActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFaithfulBoundary
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import LeanFormal.IUT.IUTIII.Theorem311.Output.CarrierConnectorSpecification
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceColumnCarrierIdentification

/-! # S1161: Core Choice + LinkSpan from a source input

Audit/construction only from existing objects.  A `DerivedPrerequisiteInput`
already carries an actual `Core Label Choice` (`I.core`), and `LinkSpan.refl`
gives an actual LinkSpan on it.  The conditional carrier/presentation wiring
reuses `carrierOfConnectorDatum` and `sourcePresentationOfCarrier`.

Still absent: any map from `FPrimeStrip V` to this Choice type.  The exact
minimum for that bridge is a source-level realization of the Choice carrier
together with CC.1/CC.2 (`CarrierConnectorDatum`), W.1
(`SourceProcessionAutomorphismData`) and W.4 (`Ind2ActionData`); W.3 explicitly
has no FPrimeStrip-to-Choice correspondence in the tree.
No new wrapper object is introduced. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1161CoreChoiceBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.CarrierConnectorSpecification
open LeanFormal.IUT.SourceMultiradialPresentationWiring

universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- Actual Core Choice carried by a derived source input. -/
noncomputable def sourceCoreOfDerived
    (I : DerivedPrerequisiteInput Label Choice) :
    MultiradialKernel.Core Label Choice :=
  I.core

/-- Actual LinkSpan on that core, by the identity link. -/
noncomputable def sourceLinkSpanOfDerived
    (I : DerivedPrerequisiteInput Label Choice) :
    LinkSpan (sourceCoreOfDerived I) (sourceCoreOfDerived I) :=
  LinkSpan.refl (sourceCoreOfDerived I)

@[simp] theorem sourceLinkSpanOfDerived_left
    (I : DerivedPrerequisiteInput Label Choice) (c : Choice) :
    (sourceLinkSpanOfDerived I).left c = c := rfl

@[simp] theorem sourceLinkSpanOfDerived_right
    (I : DerivedPrerequisiteInput Label Choice) (c : Choice) :
    (sourceLinkSpanOfDerived I).right c = c := rfl

/-- Conditional carrier from CC.1/CC.2; reuses the existing constructor. -/
noncomputable def sourceCarrierOfDerived
    (I : DerivedPrerequisiteInput Label Choice)
    (datum : CarrierConnectorDatum I.core) :
    ParametricTheorem311.Carrier Label Choice :=
  carrierOfConnectorDatum I.core I.profile datum

#check sourceCoreOfDerived
#check sourceLinkSpanOfDerived
#check sourceCarrierOfDerived
#check CarrierConnectorDatum
#check SourceProcessionAutomorphismData
#check Ind2ActionData

end LeanFormal.IUT.XiFPaper.S1161CoreChoiceBridgeActual
end
