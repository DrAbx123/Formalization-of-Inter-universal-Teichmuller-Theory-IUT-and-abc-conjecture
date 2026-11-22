# Concrete source comparison: numerical truth analysis

Date: 2026-10-28
Scope: analysis only; no Lean compilation.

## 1. Actual Gaussian data at q = 1/5

For a prime l >= 5:

- SignedLabel l.value = { j : Int | |j| <= lStar l.value }, with
  lStar l = (l-1)/2.
- card(SignedLabel l.value) = l.value.
- gaussExponent j = j^2.
- gaussExponentSum l = sum_{j=-k}^{k} j^2, k = (l-1)/2
  = k(k+1)(2k+1)/3.

For l = 5:

| quantity | value |
|---|---|
| lStar(5) | 2 |
| card(SignedLabel 5) | 5 |
| gaussExponentSum(5) | 0^2 + 1^2 + 2^2 + 1^2 + 2^2 = 10 |
| coefficient gaussExponentSum / card | 10 / 5 = 2 |
| signed average at q = 1/5 | log(5) * 2 = log(25) |

Thus the actual Gaussian signed theta average at q = 1/5 is

  signedAverage = log 25 = 2 log 5 > 0.

## 2. q-pilot magnitude if q = 1/5 is treated as the q-pilot scalar

If a single q-pilot q is 1/5, then

  |log q| = |log(1/5)| = log 5,

and the paper q-pilot signed log-volume is

  -|log q| = -log 5.

The concrete source comparison used in the current files is the inequality

  signedAverage <= sourceBadQAbsLog I.initial,

where sourceBadQAbsLog is the sum of the actual bad q-parameter absolute logs.

If one substitutes q = 1/5 as the only bad q, then

  sourceBadQAbsLog = log 5,

but

  signedAverage = log 25 = 2 log 5 > log 5.

Therefore the comparison in the single-q = 1/5 interpretation is **false**,
not merely unproved.

## 3. Paper q is the q_v product, not a single q_v

IUT III defines the q-pilot object from the collection of q_v for v in V_bad.
If the paper q is the product of the local q_v, then the correct q-pilot scalar
is

  q_pilot = product_{v in V_bad} q_v

and its absolute log is

  |log q_pilot| = sum_{v in V_bad} |log q_v|,

with the corresponding signed q-pilot log-volume

  - sum_{v in V_bad} |log q_v|.

The concrete theta packet value q = 1/5 is a **theta packet parameter**, not
the global product of the q_v family. Treating 1/5 as the q-pilot q is a
category error: it is one local/theta-side value, not the product over V_bad.

## 4. Correct q candidate

The correct q candidate for the q-pilot object should be

  q_pilot = product_{v in V_bad} q_v,

using the actual q_v family:

- qVFamily at the actual clause-B F-lift candidates, or
- the base-q family under the actual completionMap/preimage comparison.

The corresponding exact source-q equality needed for the paper log-volume is

  sourceQPilotSignedLog I.initial
    = - sum_{v in V_bad} |log q_v|
    = localSignedLog C3.q

only when C3.q itself is the product q_pilot (or an aggregate q whose signed
log is exactly the sum). This equality is the missing source identification
recorded in ConcreteSourceQIdentificationActual.lean; it is not implied by
q = 1/5.

## 5. Truth verdict

1. For l = 5 and the Gaussian theta packet q = 1/5:
   signedAverage = 2 log 5.
2. If the q-pilot scalar is taken to be the single value 1/5, then
   the comparison signedAverage <= |log q| is false because 2 log 5 > log 5.
3. The paper q-pilot q is the q_v product; the correct comparison is
   signedAverage <= sum_{v in V_bad} |log q_v|.
4. Whether the product comparison holds depends on the actual q_v family, not
   on the theta packet value 1/5. At least the single-q substitution is
   numerically false, so any source comparison that uses q = 1/5 as the
   q-pilot scalar must be rejected.
5. The correct q candidate is product_{v in V_bad} q_v, and its q-pilot
   log-volume is -sum_v |log q_v| in the actual source normalization.

## References

- gaussExponent / SignedLabel: LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean,
  SignedLabelEquiv.lean.
- gaussExponentSum and Gaussian signed average formula:
  tmp/sheaf/xif/paper/SignedAverageBoundActual.lean.
- Concrete comparison numeric reduction:
  tmp/sheaf/xif/paper/ConcreteSourceComparisonNumericActual.lean.
- q_v product/source-q identification obstruction:
  tmp/sheaf/xif/paper/ConcreteSourceQIdentificationActual.lean.
