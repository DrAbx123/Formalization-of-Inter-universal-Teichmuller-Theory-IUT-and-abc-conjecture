import LeanFormal.IUT.IUTII.Kummer.SourceLogShellXMuPacket
import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment

/-!
# Mzk1ThetaPilotPreciseInterfaceActualAdapted (adapted copy, A475 reuse) — precise theta-pilot/X-mu packet interface
(paper precision layer, asset-first)

STEP 0 prior-art (reused, no new mathematics):
* IUTII/Kummer/SourceLogShellXMuPacket: sourceLogShellXMuPacket, SourceLogShellXMuChainSupply,
  chainEquiv and its log-shell image / IQ-span / packet transport theorems;
* IUTII/Kummer/SourceThetaPilotIQContainment: one-place family, product comparison, tensor
  generator, IQ packet, generator membership.

WHAT THIS FILE DOES: re-exports the precise X-mu chain-supply and theta-pilot packet data as
named interface declarations (a typed precision layer), and records the rows.  The paper's
construction of the precise theta-pilot object is NOT asserted.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPreciseInterfaceActualAdapted

open LeanFormal.IUT

/-- The X-mu chain supply (precise theta-pilot transport data). -/
def xmuChainSupply :=
  @SourceLogShellXMuChainSupply

/-- The composed chain equivalence of an X-mu chain supply. -/
def xmuChainEquiv :=
  @chainEquiv

/-- The chain equivalence maps the D-log-shell onto the F-log-shell. -/
def xmuChainEquiv_image_logShell :=
  @chainEquiv_image_logShell

/-- The left packet map sends the D-IQ packet onto the X-packet. -/
def xmuLeftPacketMap :=
  @left_packet_map

/-- The composed packet map sends D-packet onto F-packet. -/
def xmuPacketMap :=
  @packet_map

/-- The source log-shell one-place family. -/
def xmuOnePlaceFamily :=
  @sourceLogShellOnePlaceFamily

/-- The theta-pilot product comparison on the one-place packet. -/
def thetaPilotProductComparison :=
  @sourceThetaPilotProductMap

/-- The theta-pilot IQ packet inside the one-place packet. -/
def thetaPilotIQPacketSubmodule :=
  @sourceThetaPilotIQPacket

/-- The log-shell tensor generator lies in the theta-pilot IQ packet. -/
def thetaPilotGenerator_mem_IQ :=
  @sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket

/-- Precision rows: (paper object, formal interface, status). -/
def thetaPilotPreciseRows : List (String × String × String) :=
  [ ("X-mu chain supply (precise theta-pilot transport)", "SourceLogShellXMuChainSupply (re-exported as xmuChainSupply)", "TREE ASSET (re-exported)"),
    ("chain equivalence and log-shell image", "chainEquiv / chainEquiv_image_logShell", "TREE PROOF (re-exported)"),
    ("packet transport D -> X -> F", "left_packet_map / packet_map", "TREE PROOF (re-exported)"),
    ("one-place source log-shell family", "sourceLogShellOnePlaceFamily", "TREE ASSET"),
    ("theta-pilot product comparison", "sourceThetaPilotProductMap", "TREE PROOF"),
    ("theta-pilot IQ packet + generator membership", "sourceThetaPilotIQPacket / sourceLogShellTensorGenerator_mem_sourceThetaPilotIQPacket", "TREE PROOF"),
    ("paper precise theta-pilot object construction", "not asserted: precision interface only", "NAMED (paper input)") ]

/-- The precision row record has seven rows. -/
theorem thetaPilotPreciseRows_length : thetaPilotPreciseRows.length = 7 := rfl

#check xmuChainSupply
#check xmuChainEquiv
#check xmuChainEquiv_image_logShell
#check xmuLeftPacketMap
#check xmuPacketMap
#check xmuOnePlaceFamily
#check thetaPilotProductComparison
#check thetaPilotIQPacketSubmodule
#check thetaPilotGenerator_mem_IQ
#check thetaPilotPreciseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPreciseInterfaceActualAdapted
end
