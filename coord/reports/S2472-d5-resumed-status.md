# S2472: D5 large-image resumed status

Date: 2026-11-03. LOCK released. Serial lake env lean -j1 compiles performed.

## Serial gate compilation

All four compiled EXIT=0, one process at a time:
- S2440RangePairTransitiveSubagentActual (serial, axioms trio)
- S2442QE5DegreeOrderSubagentActual (serial, axioms trio)
- S2445D5LargeImageChainActual (serial, axioms trio)
- S2449D5FinalStatusActual (serial, axioms trio)

New clean integration S2472D5GateActual.lean: EXIT=0.
source 2197 B SHA256 de9787ffc5beb6e79acd04648adb97207e1dbed31926b0e3d49a59f854fbeb83
olean 20384 B SHA256 c17cb1b6e0282096a3dda98465802154611e05b4c4f584294ce5e572234d6aa3
Axioms of S2472D5LargeImageFive_of_exact / S2472Pair_of_imageTail /
S2472Pair_of_twelveCycle / S2472CycleRequired_iff:
propext, Classical.choice, Quot.sound.

## D5 exact missing

S2472ExactMissing = S2472PairRequired AND S2472CycleRequired, where
- S2472PairRequired = S2203RangePairTransitiveRequired S1982Basis;
- S2472CycleRequired = S2203RangeCycleTypeRequired S1982Basis.

Conditional D5 only:
  S2472D5LargeImageFive_of_exact : S2472ExactMissing -> S1987D5LargeImageFive.

No actual S1987D5LargeImageFive.

## PairTransitive

Actual reductions (S2440): SL2 pair-transitive; ImageTail -> pair; large image ->
pair; twelve-cycle -> pair; under cycle type pair <-> ImageTail; basis
independence.

Exact missing still pair transitivity of the actual range. Sufficient inputs:
S1725ImageTail, S2440TwelveCycleInputRequired, or a proved 12-cycle in the
range. The 12-cycle route still needs the mod-13 certificate and the
Dedekind-Frobenius root cycle comparison.

## HasCycleType102

Attempting to compile the current S2461CycleTypeFinalActual failed EXIT=1 with
errors (Finset.insert, Galois transport, HSMul) and sorryAx; it is INVALID and
must not be consumed. The exact target remains
S2203RangeCycleTypeRequired S1982Basis.

Required: a repaired mod-29 factorization object (old S2057Mod29FactorizationData
is false; true product has scalar 4), Dedekind-Frobenius cycle comparison at a
prime above 29, and Q-to-F' transport/linear disjointness.

## Subagents

A3 pair-transitivity subagent has a partial probe file
S2470PairTransitiveFinalActual.lean (3962 B) with no olean; not verified.
B3 cycle-type subagent has no file yet.
No subagent output is consumed as actual.

## Degree 480

Not mentioned as a target. S2442 remains the refutation/correction: s2289QE5
degree is 240 under the projective bridge. No degree-480 claim is made.

## Next serial steps

1. Recompile S2472 after any integration edit.
2. Recompile any new A3/B3 file only when complete; require EXIT=0/olean/axioms.
3. To close D5: prove pair/cycle at S1982Basis (Dedekind-Frobenius + finite
certificates), then S2472D5LargeImageFive_of_exact.