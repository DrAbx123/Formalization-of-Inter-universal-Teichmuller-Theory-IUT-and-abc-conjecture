# S51: decoration index/wrapper and per-consumer decoration status

Date: 2026-10-29.

## Actual wrapper

The Lean core has only DPrimeStrip and FPrimeStrip.  S51 adds

  inductive Decoration := vdash | turnstile | dashv | theta
  DecoratedDPrimeStrip (delta : Decoration) V := strip : DPrimeStrip V
  DecoratedFPrimeStrip (delta : Decoration) V := strip : FPrimeStrip V

so different paper decorations are no longer forced to be the same type.

## Per-consumer decoration status

| Consumer | Decoration read from source | Status |
|---|---|---|
| DThetaShadow.dStrip | D-Theta (source DThetaShadow is the D-theta shadow) | assigned theta |
| I.fPrimeStripAt used by Ind1/Ind2/Ind3 | not named in the type/definition | missing |
| IPLAPT strips | not named in the type/definition | missing |
| GlobalThetaPilotStrip | not named in the type/definition | missing |
| ConcretePaperQPilotWitness.stripTarget | not named in the type/definition | missing |

The source definitions for the missing consumers use a bare FPrimeStrip with no
decoration field, so assigning a paper decoration would be a guess.  The exact
missing per-consumer decoration map is recorded in
missingDecorationConsumers in the Lean file.

## O decorations

Not treated in S51; see S47 for O^x/O^mu/O-triangle gap.

No fake decoration assignment, equality, sorry, axiom, True, or PUnit.
