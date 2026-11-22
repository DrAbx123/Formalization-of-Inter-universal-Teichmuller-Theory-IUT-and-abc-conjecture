/-
  Owned read-only audit probe for contract source_theorem311_assembly-v1.

  Scope limits (deliberate):
  * Only public signatures of declarations are requested via #check.
  * No source body printing, no #print / #print equations / set_option pp.all.
  * Axiom queries are limited to the assembly layer owned by this contract.
  * Run against the pre-existing cached environment only; no `lake build`,
    no rebuild of sources, no rebuild of any repairing ledger/dependency.

  Purpose of this revision: the first run showed the cached
  `SourceTheorem311Assembly` object artifact is older than the current .lean
  source (it lacks the ArrowLedger/Completion/Projection declarations and the
  qualified realization name). This revision (a) uses fully qualified names and
  (b) probes for the presence/absence of current-source-only declarations, to
  record exactly which parts of the environment are stale.
-/
import LeanFormal.IUT.IUTIII.Theorem311.SourceTheorem311Assembly

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/- A. Cross-boundary public signatures (expected in the stale cache if they
     predate the current source revision). -/
#check @SourceHodgeTheaterBridge.SourceTheorem311Realization
#check @SourceP1P2Bundle
#check @SourceP1P2Input
#check @SourceInternalWiring

/- A2. Staleness markers: declarations that exist in the current .lean sources
      of this contract's whitelist. Success here means the cached environment
      is current for that module; failure means it is stale. -/
#check @SourceTheorem311Layers.source_theorem311_layers_status
#check @SourceTheorem311ArrowLedger
#check @SourceTheorem311Completion
#check @SourceTheorem311Projection

/- B. The three owned layers and their entry points. -/
#check @SourceTheorem311Layers
#check @SourceTheorem311Layers.assemble
#check @SourceTheorem311Layers.t1_part
#check @SourceTheorem311Layers.t1_source
#check @SourceTheorem311Layers.t2_part
#check @SourceTheorem311Layers.t3_part
#check @SourceTheorem311Layers.output_parts
#check @SourceTheorem311Layers.t1_ind1_descent
#check @SourceTheorem311Layers.output_labelled
#check @SourceTheorem311Layers.output_horizontal
#check @SourceTheorem311Layers.output_evaluation

/- C. Axiom audit of THIS layer only (kernel assembly, not paper fidelity). -/
#print axioms SourceTheorem311Layers.t1_part
#print axioms SourceTheorem311Layers.t2_part
#print axioms SourceTheorem311Layers.t3_part
#print axioms SourceTheorem311Layers.assemble
#print axioms SourceTheorem311Layers.t1_ind1_descent
#print axioms SourceTheorem311Layers.output_labelled
