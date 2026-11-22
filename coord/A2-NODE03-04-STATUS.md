# A2 node03/node04 status (2026-11-15)

## Green via watchdog
- `Mzk1A2QuotientMorphismActual` — degenerate sign action/quotient morphism (pre-existing).
- `Mzk1A2Node03QuotientStackProducerActual` — `A2QuotientStackProducerData` (witness fields) + `toWitness`; DONE 02:46:38.
- `Mzk1A2Node03QuotientStackConsumerActual` — consumer + nonempty; DONE 02:48:48.
- `Mzk1A2Node03GroupsExtensionActual` — `A2Node03GroupsExtensionData`; DONE 02:59:15.
- `Mzk1A2Node03SourceSignQuotientAssemblyActual` — exact assembly interface; DONE 03:09:46.
- `Mzk1A2Node03AssemblyConsumerActual` — assembly consumer; DONE 03:14:14.
- `Mzk1A2Node03UniqueInvolutionActual` — corrected nonidentity quantifier; DONE 03:17:20.
- `Mzk1A2Node03RemainingFieldsActual` — bundle; DONE 03:19:42.
- `Mzk1A2Node03SourceVFieldsActual` — V/epsilon fields; DONE 03:21:54.
- `Mzk1A2Node03VFieldsConsumerActual` — V+producer consumer; DONE 03:23:45.
- `Mzk1A2Node03FullDataActual` — full bundle; DONE 03:26:00.
- `Mzk1A2Node03FullDataConsumerActual` — consumer; DONE 03:29:34.
- `Mzk1A2Node03IntegrationActual` — interface stack; DONE 03:31:50.
- `Mzk1A2Node03IntegrationConsumerActual` — consumer; DONE 03:34:05.
- `Mzk1A2Node03CompletionConsumerActual` — `SourceCompletionSignQuotient` consumer; DONE 03:37:40.
- `Mzk1A2Node03Node04HandoffActual` — exact handoff; DONE 03:41:31.
- `Mzk1A2Node04HandoffConsumerActual` — handoff consumer; DONE 03:44:17.
- `Mzk1A2Node04LocalTransportInterfaceActual` — local transport/unit quotient interface; DONE 03:48:08.
- `Mzk1A2Node04LocalTransportConsumerActual` — consumer; last DONE 04:01:47 (extension V/toNode03 added; check latest).
- `Mzk1A2Node03Node04AxiomProbeActual` — probe DONE 05:06:10; all six declarations use only [propext, Classical.choice, Quot.sound], no sorryAx.

## Exact interfaces without inhabitants
- `A2QuotientStackProducerData`, `A2Node03Interface`, `A2Node04HandoffData`, `A2Node04LocalTransportInterface` (and their `...Required : Prop := Nonempty ...`).
- TaskE exact interfaces: `CompletionFieldQFiveEquiv`, `IntegersCompletionFieldZFiveEquiv`, `UnitsTorsionQuotientEquiv`, `WQuotientFiveEquiv` (WQuotient construction owned by stepxi).

## Open mathematical gaps
1. Actual quotient stack `[U/G]` construction: witness fields only; no inhabitant of `A2QuotientStackProducerData`.
2. Actual groups/K-extension data: `A2Node03GroupsExtensionData` interface only; no inhabitant.
3. V/epsilon geometric tuple: `A2Node03SourceVFieldsData` interface only; no inhabitant.
4. Corrected unique-involution field is weaker than `SourceSignQuotientData.unique_elliptic_involution`; consumer migration not performed (semantic fix pending with consumers).
5. Node04 relative norm/q contraction (§7.1) and Fmod/completion transport (§7.2) not started as interfaces; WQuotient §7.4 owner stepxi.

## No fake
- No sorry/axiom/True/PUnit; no inhabitant asserted for the exact interfaces; all green achieved via watchdog only.
