import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceColumnCarrierIdentification

/-! # S1152: FPrimeStrip V vs reduced Choice/Output bridge audit

Audit only; reuses existing declarations, no new wrapper.

Findings:
* SourceFTimesMuPrimeStrip is the actual F-prime-strip + times-mu carrier
  (FPrimeStrip V plus timesMu fibers, torsion quotient, action, degree), with
  actual full poly-isomorphism classes.
* SourcePolyIsoTransportLaws is the reduced Core Label Choice / LinkSpan
  shell.  Its docstring states explicitly that no type-level bridge from the
  source records to this shell is constructed; CardIPLTransportSupply O1-O4
  are hypotheses, not a source instantiation.
* SourceColumnCarrierIdentification R6 records the finite concrete column
  realization and conditional readback, and explicitly says the strip-level
  Kummer/evaluation interfaces are not type-composable with it: there is no
  strip-to-Choice dictionary.

So there is no actual FPrimeStrip V -> Core Label Choice bridge in the tree.
The exact minimum is a type-level source realization: a Core Label Choice (or
carrier equivalence) together with LinkSpan and a CardIPLTransportSupply
discharging O1-O4; the finite concreteInput instance is the only actual
Choice-side realization (R6). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1152FPrimeStripBridgeAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.SourceColumnRealization

universe u v w uv umon upi
variable {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label]

#check SourceFTimesMuPrimeStrip
#check SourceFTimesMuPrimeStrip.canonical
#check SourceFTimesMuPrimeStripEquivalence
#check SourceFTimesMuPrimeStripFullPolyIsomorphism
#check SourceFTimesMuPrimeStripPolyIsomorphismSquare
#check LinkSpan
#check LinkSpan.Rel
#check CardIPLTransportSupply
#check polyIsoRel
#check CardIPLExchangeShape
#check coreColumnRealization
#check RealizationReadback
#check concreteInput_readback

end LeanFormal.IUT.XiFPaper.S1152FPrimeStripBridgeAuditActual
end
