# PaperThetaMagnitudeSignedActual: type/universe gap audit

Date: 2026-10-29. Analysis only; no math change.

## Observed errors

Targeted build of PaperThetaMagnitudeSignedActual.lean reports:

1. At actualSignedHull:
   actualSignedC3_hlog D has type
     ThetaPacketLogVolumeNonpos (actualSignedC3 D)
   but is expected to have type
     ThetaPacketLogVolumeNonpos (sourceTheaterC3Signed D).

2. actualSignedHull_procession_eq: rfl does not see
   (actualSignedHull ...).procession and
   c3ThetaSignedProcession (actualSignedC3 D) as definitionally equal.

3. SignedThetaAverageLeQMagnitude contains universe level metavariables at
   c3ThetaSignedProcession.{ua,uv,upi,umon,ui,?u.59,?u.58} (actualSignedC3 D)
   and paperQPilotLogMagnitude.{...,?u.74,?u.73} (actualSignedC3 D).

## Root cause

The mismatch is NOT principally SourcePilotRegionDonors vs
SourcePilotRegionData.  Both sourceTheaterC3Signed and actualSignedC3 accept
SourcePilotRegionDonors D and both produce SourcePilotRegionData.

The actual root cause is universe-level inference at the abbreviations:

- actualSignedC3 is an abbreviation for
    sourceTheaterC3Signed (l:=l) (V:=V) (I:=I) D.
  It is elaborated with two unconstrained universe metavariables.
- c3ThetaSignedProcession and paperQPilotLogMagnitude are universe-polymorphic
  with extra universe parameters not determined by C3.  Their applications in
  this file therefore carry ?u.59/?u.58 and ?u.74/?u.73.
- Because actualSignedC3 and sourceTheaterC3Signed are elaborated with
  different universe metavariables, their results are no longer defeq, so:
    * hlog's type does not match the expected argument type;
    * rfl for the procession equality fails;
    * the signed comparison definition contains universe metavariables.

## Exact type/bridge fixes (no math change)

Option A (preferred): pin the universe parameters at the call sites, e.g. use
explicit universe applications for c3ThetaSignedProcession and
paperQPilotLogMagnitude with the same extra universes as in their declarations.
This removes ?u.59/?u.58 and makes actualSignedC3 D and sourceTheaterC3Signed D
elaborate at the same levels.

Option B: replace the actualSignedC3 abbreviation by the direct call
sourceTheaterC3Signed (l:=l) (V:=V) (I:=I) D everywhere in this file, and state
actualSignedC3_hlog with target sourceTheaterC3Signed D.  Then the hlog argument
matches sourceTheaterSignedPaperSignedHull exactly.  This is a type-only bridge.

Option C: define file-local monomorphic wrappers for the signed procession and
q-pilot magnitude (fixed universes), and use those in
SignedThetaAverageLeQMagnitude and actualSignedHull_procession_eq.

None of these changes the mathematical objects.  The failing equality is a
definitional/universe issue, not a false mathematical equality.

## Status

Not patched in this pass because local compilation is disallowed for this task
and the extra universe parameter order of c3ThetaSignedProcession /
paperQPilotLogMagnitude must be read off their actual declarations before adding
explicit universe applications.  No fake theorem or rfl workaround was added.
