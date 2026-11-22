import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment

/-!
# Mzk1ThetaPilotPacketInterfaceActual — source theta-pilot packet interface (iuti-ii)

STEP 0 prior-art: LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment (one-place
source log-shell packet, product comparison, tensor generator, IQ packet membership, general
orbit containment) -> REUSE; no new mathematics, no high-level wiring.

This file re-exports the theta-pilot packet data as named interface declarations (one-place
log-shell family, tensor packet, product map and its tprod evaluation, tensor generator,
IQ-packet membership, possible-image orbit containment), and records the exact rows with
their tree sources.  The deep source-to-arithmetic comparison (the remaining named input of
the Kummer/theta interface) is NOT asserted.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual

open LeanFormal.IUT

/-- The one-place source log-shell family of a source log-shell datum. -/
def onePlaceLogShellFamily :=
  @sourceLogShellOnePlaceFamily

/-- The one-place source theta-pilot tensor packet. -/
def onePlacePacket :=
  @SourceThetaPilotOnePlacePacket

/-- The canonical product comparison on the one-place packet. -/
def productComparison :=
  @sourceThetaPilotProductMap

/-- Evaluation of the product comparison on a pure tensor. -/
def productComparison_tprod :=
  @sourceThetaPilotProductMap_tprod

/-- The source log-shell tensor generator with prescribed coordinates. -/
def tensorGenerator :=
  @sourceLogShellTensorGenerator

/-- The product comparison applied to the tensor generator. -/
def productComparison_tensorGenerator :=
  @sourceThetaPilotProductMap_sourceLogShellTensorGenerator

/-- The source theta-pilot IQ packet. -/
def iqPacket :=
  @sourceThetaPilotIQPacket

/-- The tensor generator lies in the IQ packet when every coordinate is in the log-shell. -/
def tensorGenerator_mem_iqPacket :=
  @sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket

/-- Possible-image orbit containment for an arbitrary tensor packet. -/
def possibleImage_orbitContainment :=
  @possibleImage_subset_of_generator_mem

/-- Theta-pilot packet interface rows: (item, tree source, status). -/
def thetaPilotPacketRows : List (String × String × String) :=
  [ ("one-place log-shell family", "sourceLogShellOnePlaceFamily (D.K at the singleton place)", "TREE ASSET (re-exported)"),
    ("one-place tensor packet", "SourceThetaPilotOnePlacePacket = TensorPacket family ()", "TREE ASSET (re-exported)"),
    ("product comparison + evaluation on pure tensors", "sourceThetaPilotProductMap / sourceThetaPilotProductMap_tprod", "TREE PROOF (re-exported)"),
    ("source log-shell tensor generator + product formula", "sourceLogShellTensorGenerator / sourceThetaPilotProductMap_sourceLogShellTensorGenerator", "TREE PROOF (re-exported)"),
    ("IQ packet membership of the generator", "sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket", "TREE PROOF (re-exported)"),
    ("possible-image orbit containment", "possibleImage_subset_of_generator_mem", "TREE PROOF (re-exported)"),
    ("source-to-arithmetic comparison / N4-N7 deep input", "not asserted", "NAMED (paper deep input; not proved here)") ]

/-- The theta-pilot packet row record has seven rows. -/
theorem thetaPilotPacketRows_length : thetaPilotPacketRows.length = 7 := rfl

#check onePlaceLogShellFamily
#check onePlacePacket
#check productComparison
#check productComparison_tprod
#check tensorGenerator
#check productComparison_tensorGenerator
#check iqPacket
#check tensorGenerator_mem_iqPacket
#check possibleImage_orbitContainment
#check thetaPilotPacketRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual
end
