/-
  Audit probe for the repaired SourcePacketDegreeLedger module.
  Public metadata only: elaborated public types of the changed declarations
  and names-only axiom dependencies.  Declaration values and proof bodies are
  not printed.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourcePacketDegreeLedger
import Lean

set_option maxHeartbeats 0

namespace LeanFormal.IUT.Theorem311Source.OriginalInput

set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
#check columnProcessionSourceLedger_inclusion_action
set_option pp.all false

#check columnProcessionSourceLedger_inclusion_action
#check columnProcessionSourceLedger_inclusion_degree
#check TranslatedColumnSourceLedger.component_source
#check TranslatedColumnSourceLedger.component_action
#check SpokeColumnSourceLedger.component_source
#check SpokeColumnSourceLedger.component_action
#check translatedColumnSourceLedger_zero
#check translatedColumnSourceLedger_add
#check translatedColumnSourceLedger_inverse
#check translatedColumnSourceLedger_action
#check translatedColumnSourceLedger_component
#check spokeColumnSourceLedger_action
#check spokeColumnSourceLedger_comp
#check H1H2PacketDegreeLedger.top_cardinality
#check H1H2PacketDegreeLedger.horizontal_natural
#check H1H2PacketDegreeLedger.spoke_natural
#check h1H2PacketDegreeLedger_horizontal_natural
#check h1H2PacketDegreeLedger_spoke_natural

#print axioms columnProcessionSourceLedger_inclusion_action
#print axioms columnProcessionSourceLedger_inclusion_degree
#print axioms TranslatedColumnSourceLedger.component_source
#print axioms TranslatedColumnSourceLedger.component_action
#print axioms SpokeColumnSourceLedger.component_source
#print axioms SpokeColumnSourceLedger.component_action
#print axioms translatedColumnSourceLedger_zero
#print axioms translatedColumnSourceLedger_add
#print axioms translatedColumnSourceLedger_inverse
#print axioms translatedColumnSourceLedger_action
#print axioms translatedColumnSourceLedger_component
#print axioms spokeColumnSourceLedger_action
#print axioms spokeColumnSourceLedger_comp
#print axioms H1H2PacketDegreeLedger.horizontal_natural
#print axioms H1H2PacketDegreeLedger.spoke_natural
#print axioms h1H2PacketDegreeLedger_horizontal_natural
#print axioms h1H2PacketDegreeLedger_spoke_natural
#print axioms columnProcessionSourceLedger
#print axioms translatedColumnSourceLedger
#print axioms spokeColumnSourceLedger
#print axioms h1H2PacketDegreeLedger

end LeanFormal.IUT.Theorem311Source.OriginalInput

namespace LeanFormal.IUT

#print axioms FPrimeStripEquiv.compatAction
#print axioms FPrimeStripEquiv.compatDegree

end LeanFormal.IUT

namespace LeanFormal.IUT.Theorem311Source.OriginalInput

#print axioms fLinkAt_refl
#print axioms fLinkAt_trans
#print axioms fLinkAt_action
#print axioms fLinkAt_degree
#print axioms stageSpoke_comp_component

end LeanFormal.IUT.Theorem311Source.OriginalInput
