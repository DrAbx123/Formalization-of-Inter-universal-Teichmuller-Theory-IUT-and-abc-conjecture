# PAPERN8 semantic audit

Date: 2026-10-24
Owner: transport
Scope: read-only audit of C9PaperClosure.lean, PaperN8Closure.lean,
C9QThetaValuesNamed.lean. No Lean edits.

## Files and exact versions

- tmp/sheaf/n8/closure/C9PaperClosure.lean, lines 150,
  SHA256 3094125B1462769E1FD641F4BBDF3DA8A3609D7E3E6F4C0A7BE1C215E49A20BB
- tmp/sheaf/n8/closure/PaperN8Closure.lean, lines 137,
  SHA256 C83E30AF756593AE9CA6759DBC6DAB22E64F95F60696B709173990AF698B116F
- tmp/sheaf/n8/closure/C9QThetaValuesNamed.lean, lines 104,
  SHA256 90D48BBBBB07229072ADB19133F7DB9C6E882AB701779E2DD016E9D202ADEAC4

## 1. Target class

C9PaperClosure.PaperC9Output contains source fields chainA, theta,
valuesWitness AND a field:

  comparison : P6Exact X (QNamed X chainA) OR P6Epsilon X (QNamed X chainA)

This makes the P6 comparison part of the target structure.  The named sorry
paperC9Output_nonempty : Nonempty (PaperC9Output X mu) therefore assumes an
instance of the P6 comparison as part of the package it constructs.  It is not
a theorem that P6 holds for the source data.

Verdict: target-class problem.  The comparison is a conclusion, not source
data.  Source package and P6 comparison must be separated.

PaperN8Closure.PaperN8Output contains fields:

  valuesBounded : forall z, z in values -> z <= theta
  q_le_theta : q <= theta

These are the two paper conclusions.  They are supplied by named-sorry
obligations in paperN8Closure_nonempty; they are not proved from source data.
The structure is an output package that contains its own conclusion fields.

C9QThetaValuesNamed contains only definitions and three named object-existence
sorries (missing_q_source, missing_theta_source, missing_values_source).  It
does not state Q <= Theta or ValuesBounded.  Target class is source-object
existence, but the objects are too abstract (sections 3/4).

## 2. P6 J range

P6Comparison.SourceAllowedOutput X is a good J carrier: its fields do not
mention Q, Q <= Theta, or the desired equality; P6Exact/P6Epsilon quantify over
J : SourceAllowedOutput X only.  The P6 quantifier range is independent of Q.

Two wrapper definitions are semantically wrong:

- C9PaperClosure.ComparisonSourceRange has type Set (Type _) and is
  {Y | Y = P6Comparison.SourceAllowedOutput X}.  This is a set of TYPES
  containing one type, not a set of J values; it cannot serve as the J range.
- PaperN8Closure.PaperComparisonJRange has the same type-level error.

Exact fix: delete both definitions.  If a range constant is needed, use
Set (SourceAllowedOutput X) := Set.univ, or state J : SourceAllowedOutput X
directly in P6Exact/P6Epsilon.  Do not expose a set of types as source range.

## 3. Q / Theta / Values free-field status

### Q
QNamed C := P6ChainA.Q C, and QNamed_eq_nativeScalar proves it equals the
actual native q scalar qPilotSignedLog X.  Q is not a free Real field.

Caveat: P6ChainAData.globalLq : GlobalLqDonor X, whose readout is a free
function constrained only at p6ChainALocal X by readout_eq_local.  Q is forced
by that one equality, so the Q value is actual; the readout interface is weak
but does not make Q free.

### Theta
ThetaNamed R := R.ellOutValue where R : ThetaSourceObject, which is a
P6L.P6Readout.  P6Readout has free fields support, weight, dimension,
reference, region, value with value_eq : value = ellOut ... reference region.
value is computed, and Adm constrains reference/region, but weight, dimension,
support, reference and region are donor-selected fields.  This is an exact
source-object gap, not an actual ThetaPaper construction; no tie to the C4
possible-theta image or C9Paper thetaHull.

### Values
ValuesNamed := {z | exists R : ValuesSourceObject, z = R.ellOutValue}.
ValuesSourceObject is the SAME P6L.P6Readout type as Theta.  Values are all
ellOut values of arbitrary P6 readouts, not C4 output regions or determinant-
normalized values.  Theta and Values use independent P6Readout objects;
valuesWitness is not tied to theta.  ValuesNamed has no provenance/source
restriction beyond exists R.  There is no singleton (fixed), but the source
object is still the abstract P6 readout donor, not the C4/C8 ValuesPaper.

Verdict: Q is actual; Theta/Values are exact donor-gap interfaces, not claimed
completed source objects.  Do not treat ThetaNamed/ValuesNamed as proved source
Theta/Values.

## 4. ValuesBounded and Q<=Theta as inputs

### C9PaperClosure
- ValuesBounded is a definition (condition), not a proof; no named sorry in
  this file.
- QInRleqTheta is a definition; no proof.
- PaperC9Output.comparison imports the P6 conclusion into the target structure
  (section 1).  P6Exact/P6Epsilon do NOT take Q <= Theta as input: they range
  over SourceAllowedOutput X independent of Q.  This part is clean.
- paperC9Output_nonempty does not prove ValuesBounded or Q <= Theta; it only
  supplies the source record with comparison field via named sorry.

### PaperN8Closure
- PaperValuesBounded is a definition over ValuesNamed and a single P6Readout R:
  every z in ValuesNamed is <= R.ellOutValue.
- paperValuesBounded_obligation is a named sorry; it is NOT an input to the P6
  comparison (P6 comparison lives in N8RouteObligations and is independent of
  Q <= Theta).
- paperQLeTheta_obligation is a named sorry; Q and Theta are constrained by
  equalities to chainA.Q and readout.ellOutValue.  The obligation is the
  conclusion, not an input to P6.
- paperN8Closure_nonempty packages these named obligations as
  valuesBounded/q_le_theta fields.

Verdict: ValuesBounded and Q <= Theta are not hidden inputs to P6; they are
named conclusion obligations.  The remaining issue is that they are fields of
PaperN8Output, so the output structure carries its conclusions.

## 5. Exact fixes

1. Separate P6 comparison from PaperC9Output.
   Remove PaperC9Output.comparison.  Keep only source data (chainA, theta,
   valuesWitness).  Add a separate named-sorry theorem:

     theorem paperC9Comparison_obligation (O : PaperC9Output X mu) :
         P6Exact X O.Q OR P6Epsilon X O.Q := by sorry

   Then paperC9Output_nonempty no longer assumes the P6 conclusion.

2. Remove type-level J range definitions.
   Delete ComparisonSourceRange and PaperComparisonJRange.  Use
   J : P6Comparison.SourceAllowedOutput X directly or
   Set.univ : Set (SourceAllowedOutput X).

3. Tie Theta/Values to source objects.
   Replace common P6L.P6Readout aliases by:
   - Theta source object with an explicit equality to C9Paper thetaHull /
     sourceHolomorphicHull region;
   - Values source object built from C4/C8 output regions or
     P6Comparison.SourceAllowedOutput.region, not the abstract readout value.
   Keep exact named sorries for missing source constructions, but do not call
   P6Readout itself the Theta/Values object.

4. PaperN8Output: separate data from conclusions.
   Remove q_le_theta and valuesBounded from the data structure.  Keep separate
   named-sorry propositions paperValuesBounded_obligation and
   paperQLeTheta_obligation (already present) and package data only.  If a
   packaged target is needed, mark it as a named-sorry target record, not as a
   proved output.

5. ValuesBounded semantics.
   Use a single Theta/readout selected by the same source object:
   forall z in ValuesSource O, z <= ThetaSource O, with ValuesSource tied to C4
   output regions.  The current universal-over-all-P6Readout form is too strong
   and disconnected from Theta.

6. Q readout interface (lower priority).
   Q is forced to the actual q scalar at the actual local point by
   readout_eq_local, so Q is not free.  If the global L_q donor is later fixed,
   constrain GlobalLqDonor.readout on all P6 local data rather than one point.

## 6. Status summary

- C9PaperClosure: source package + named object gap acceptable, but comparison
  as a field is a target-class defect; J range def is wrong.
- PaperN8Closure: P6 comparison independent of Q<=Theta; ValuesBounded/Q<=Theta
  are named conclusions, not hidden inputs; but they are fields of the output
  package, and J range def is wrong.
- C9QThetaValuesNamed: Q actual; Theta/Values are exact donor-gap interfaces,
  not free Real fields; Values is not tied to the C4 source region and Theta/
  Values are independent P6 readouts.
- No Lean file was changed by this audit.
