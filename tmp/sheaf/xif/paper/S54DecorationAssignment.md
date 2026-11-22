# S54: actual decoration assignment for S51 consumers

Date: 2026-10-29.

## Source reading

| Consumer | Source form | Actual decoration |
|---|---|---|
| DThetaShadow.dStrip | source D-theta shadow (DThetaShadow) | D-Theta |
| I.fPrimeStripAt (Ind1/2/3) | I.primeStripAt, plain F-prime-strip | undecorated F |
| IPLAPT strips | plain F-prime-strip fields | undecorated F |
| GlobalThetaPilotStrip | I.primeStripAt 0 0, plain F-prime-strip | undecorated F |
| ConcretePaperQPilotWitness.stripTarget | concrete q-pilot F-prime-strip | undecorated F |

The four S51 missing consumers are plain F-prime-strips, not F-Vdash,
F-turnstile, F-dashv, or F-Theta.  Assigning a decorated variant would be false.

## Actual annotation

Decoration.undecorated was added to Decoration.  S54 defines SourceConsumer,
consumerDecoration, ConsumerDecorationField and consumerDecorationFields.

The source structures (FPrimeStrip and the consumer structures) have no
decoration field; the minimal actual missing source field is one
Decoration annotation per consumer, recorded by ConsumerDecorationField.
No source field is fabricated: the decoration is an external annotation read
from the paper context of each plain F-prime-strip.

No fake decoration/sorry/axiom/True/PUnit.
