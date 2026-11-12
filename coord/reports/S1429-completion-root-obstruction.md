# S1429: completion-root obstruction

Date: 2026-10-31.  Owner: S1429.  Lean:
[tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean](../../tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean).
EXIT=0.  175 lines.  SHA256
659C4F5F9B6BA081AE5B72AE49FB2D8B155503FD50A3EE21584F0C1069024A74.

## Verdict

The old C3 completion-root first field is not merely missing: it is impossible.
For every finite-place q-candidate q, there is no compatible natural root system
in the completion:

    no_completionRootSystem (q : FinitePlaceQCandidate place.val) :
      not Nonempty (NatRootSystem (candidateUnits place q)).

Consequently the old SourcePilotRegionData schema, which requires
roots : NatRootSystem qUnit with qUnit = candidateUnits place q, is
uninhabited:

    sourcePilotRegionData_isEmpty (I : OriginalInput l V) :
      IsEmpty (SourcePilotRegionData I).

This is a valuation no-go, not a construction of an L-side replacement and not a
fabricated root.  S1314's algebraic-closure carrier remains the paper-faithful
route; this file shows why the literal completion schema cannot be repaired by
adding a root.

## Exact first field

    CompletionRootCarrier place q := NatRootSystem (candidateUnits place q)
    CompletionRootObstruction place q := Nonempty (CompletionRootCarrier place q)

    completionRootObstruction_iff :
      CompletionRootObstruction place q <-> Nonempty (NatRootSystem (candidateUnits place q))

    completionRootObstruction_holds :
      not CompletionRootObstruction place q

## Proof

A q-candidate has nonzero valuation

    Valued.v q.q = WithZero.exp (-(e : Int)),   e = q.order > 0.

If a NatRootSystem existed, its root at n = e + 1 would satisfy r^n = q.
Applying Valued.v and WithZero.log gives

    (n : Int) * log (Valued.v r) = -(e : Int).

Thus n divides e, but n = e + 1 > e > 0.  Contradiction.  The argument uses
only the discrete integer valuation, the candidate law, and the NatRootSystem
power law; no algebraic closure and no extra source hypothesis are used.

## Verification

Compiled with the project's full LEAN_PATH:

    lean -j1 -R D:/lean tmp/sheaf/xif/paper/S1429CompletionRootObstructionActual.lean
    EXIT=0

Also compiled with -o to .lake/build/lib/lean/tmp/sheaf/xif/paper/
S1429CompletionRootObstructionActual.olean, EXIT=0.  The direct lean invocation
was used because lake env lean was returning -1/OOM under the concurrent Lean
load; the LEAN_PATH was identical to lake env's.

Axiom probe: tmp/sheaf/xif/paper/_S1429AxiomProbe.lean, EXIT=0.  The theorems
no_completionRootSystem, completionRootObstruction_holds,
sourcePilotRegionData_isEmpty and completionRootObstruction_iff depend only on
[propext, Classical.choice, Quot.sound].

No sorry, admit, axiom, arbitrary data, or completion root appears in the file.

## Concrete C3 specialization

An auxiliary probe (tmp/sheaf/xif/paper/_S1429ConcreteCorollaryProbe.lean,
EXIT=0) imports ConcreteC3RootTensorActual and proves

    not ConcreteC3RootTensorActual.ConcreteCompletionRootObstruction (I := I) place

for the concrete C3 input and place.  Thus the literal S1304/S1274 first field
is not only missing but empty; no completion root can inhabit it.

## Consumer and next action

Consumer: the old C3 SourcePilotRegionData root field and any downstream
completion-root C3 consumer.  The exact first field is now proved empty; the
next executable step is target-level: use the S1314 L-side actual object for C3
and retire the completion-root field.  No L-side object is constructed here.
