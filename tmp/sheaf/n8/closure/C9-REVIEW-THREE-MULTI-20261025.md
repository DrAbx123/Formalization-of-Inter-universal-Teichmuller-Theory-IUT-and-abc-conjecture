# C9 review: no-hidden-condition audit of ThreeAssumptions

Task: task-462. Reviewer: multiradial. Date: 2026-10-25.
Review only; no edits to source Lean, no Lean/Project edits, no mixed/E3.
Deliverable: this file only. target_accepted=false; C1/P6 open.

## 0. Audited file

tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean
59 lines, SHA256 E71F22D4FDD47FAA8DE1646713AF88BBCD72E2541CD8121824ABAE131E48F703.

Question: list every field, map it to the source assumption, and check whether
there is an extra/hidden condition. Is C1 derived only from the three
assumptions?

Verdict: NO. The file is a tautology: C1 is inserted as the structure field
qPilotOutput_mem (Theorem311Full, line 18), and the "unconditional" theorem
also depends on the global axiom sourceThreeAssumptions. The theorem proves
only qLog <= h for arbitrary abstract Output/logVol/h, not the source
Cor3.12/C1 inequality Q <= -|log Theta|. The hidden condition is exactly C1/
the q-pilot possible-output membership, mislabeled as "Theorem3.11 full
content".

## 1. Complete field inventory

### Theorem311Full (lines 13-18)

| field | line | type/content |
|---|---|---|
| Output | 14 | Type |
| possibleOutputs | 15 | Set Output |
| logVol | 16 | Output -> R |
| qPilotOutput | 17 | Output |
| qPilotOutput_mem | 18 | qPilotOutput in possibleOutputs |

### Prop39 (lines 21-23)

| field | line | type/content |
|---|---|---|
| qLog | 22 | R |
| qLog_eq | 23 | qLog = T.logVol T.qPilotOutput |

### Remark395 (lines 27-31)

| field | line | type/content |
|---|---|---|
| R | 28 | Set R |
| R_eq | 29 | R = T.logVol '' T.possibleOutputs |
| h | 30 | R |
| hull_upper | 31 | forall x, x in R -> x <= h |

### ThreeAssumptions (lines 34-37)

| field | line | type/content |
|---|---|---|
| T311 | 35 | Theorem311Full |
| P39 | 36 | Prop39 T311 |
| R395 | 37 | Remark395 T311 |

### Axiom (line 48)

sourceThreeAssumptions : ThreeAssumptions.

## 2. Field-by-field source mapping

### Output
Source: the multiradial construction algorithm produces a collection of
possible output data (Theorem3.11(i)); in C9 it is the multiradial output type.
The field is an arbitrary Type with no Hodge-theater, Theta-pilot,
Ind1/Ind2/Ind3, IPL/SHE/APT, log-Kummer, or normalization data. Mapping is
only a type-level placeholder, not the source output object.

### possibleOutputs
Source: the set of possible output data of the multiradial algorithm. The
field is an arbitrary Set Output, not constructed from the algorithm and not
subject to Ind1/Ind2/Ind3. No source relation.

### logVol
Source: the packet+procession-normalized mono-analytic log-volume of
Proposition3.9, with Haar/log normalization and the Ind1/Ind2 invariance and
Ind3 upper-semi-compatibility. The field is an arbitrary function
Output -> R with no additivity, normalization, monotonicity, or Ind laws.
Mapping is not source.

### qPilotOutput
Source: the q-pilot is the fixed/coric INPUT object at (1,0) in the large
volume container; it is not, by Theorem3.11 alone, one of the possible output
data of the Theta-pilot algorithm. The field selects an arbitrary Output and
calls it qPilotOutput. No source construction selects such an output.

### qPilotOutput_mem
Source: this says the q-pilot input/output is in possibleOutputs. This is
exactly the C1/xi-f membership: an actual possible output with the q-pilot
log-volume. IUT III Theorem3.11 does not contain this; xi-f asserts it only
formally/approximately and is the known gap (C9-C1-MASTER, C9-REVIEW-COR312-
QPILOT). The docstring in lines 10-12 says "Theorem3.11, full content needed
here ... the fixed/coric q-pilot input rigidification is one of them (IPL +
final evaluation map)"; that is not Theorem3.11 alone. It is Theorem3.11 plus
the C1/xi-f membership. This is the hidden condition.

### Prop39.qLog
Source: the q-pilot log-volume Q=-|log q| of Proposition3.9/Cor3.12. The field
is an arbitrary real number named qLog; qLog_eq defines it as logVol of the
chosen qPilotOutput. It is not proved equal to the source q-pilot log-volume
and has no normalization/factor d or 41.

### Prop39.qLog_eq
Source: Proposition3.9 does not say "qLog is the logVol of a selected
possible qPilotOutput"; it defines the log-volume functional and the q-pilot
log-volume. The equality is a definitional identity within the abstract
structure, not a source theorem. It is consistent with any qLog once
qPilotOutput is selected.

### Remark395.R
Source: Cor3.12 uses R_{<=-|log Theta|}, the set of possible pilot-object
log-volumes bounded by the hull log-volume; Remark3.9.5 supplies the hull/
determinant/log-volume framework. The field is an arbitrary Set R; R_eq
defines it as the logVol image of possibleOutputs. It is not the source
R_{<=-|log Theta|} and has no relation to -|log Theta|.

### Remark395.R_eq
This is a definitional identity (R is the image); it is acceptable as an
internal definition, but it means the only content is that qLog is in the
image if qPilotOutput is possible. It is not a source theorem about Remark3.9.5.

### Remark395.h
Source: h=-|log Theta| is the procession-normalized log-volume of the
holomorphic hull of the union of possible Theta-pilot images, subject to
Ind1/2/3. The field is an arbitrary real number. No source object, no hull,
no Ind, no normalization.

### Remark395.hull_upper
Source: if h is the hull log-volume and possible outputs lie in the hull, a
monotonicity inequality gives output log-volumes <= h. But the file has an
arbitrary h and arbitrary logVol; hull_upper is an extra assumed upper bound,
not derived from Remark3.9.5. It is a hidden/extra condition of the abstract
structure, though weaker/different from C1.

### ThreeAssumptions.T311/P39/R395
The structure bundles the above fields. There are no other fields, but the
fields themselves contain the hidden conditions (especially
qPilotOutput_mem and the arbitrary h/hull_upper). Bundling does not map them
to source.

### sourceThreeAssumptions
This is a global axiom asserting that a ThreeAssumptions exists. It is not a
source theorem; it packages all the hidden fields. cor312_unconditional depends
on it. The printed #print axioms would include sourceThreeAssumptions (and
the standard axioms); the theorem is "unconditional" only relative to this
axiom.

## 3. The theorem is a tautology

cor312 (lines 41-45):
  - qLog is in R because R_eq is the logVol image and qPilotOutput is in
    possibleOutputs (qPilotOutput_mem);
  - qLog <= h because hull_upper applies to that membership.
Thus cor312 is the projection:
    qPilotOutput_mem + R_eq + qLog_eq + hull_upper => qLog <= h.

It does not prove:
  - qLog = Q = -|log q| (source q-pilot value);
  - h = -|log Theta| (source hull log-volume);
  - the output qPilotOutput is an actual multiradial output with the source
    log-volume normalization;
  - R is the source R_{<=-|log Theta|};
  - Cor3.12's inequality -|log Theta| >= -|log q|.
The conclusion is an abstract qLog <= h, not C1/Cor3.12.

cor312_unconditional (lines 51-53) merely applies cor312 to the axiom
sourceThreeAssumptions. It is not a theorem from IUT source assumptions; it is
a theorem from an axiom that already contains C1 as qPilotOutput_mem.

## 4. Hidden-condition countermodel (removing qPilotOutput_mem)

Take Output = Bool, possibleOutputs = {true}, logVol true = 0, logVol false =
1, qPilotOutput = false. Set qLog = 1 (qLog_eq), R = {0} (R_eq), h = 0,
hull_upper holds for R. All fields of Theorem311Full except qPilotOutput_mem,
and all fields of Prop39/Remark395, hold. But qLog = 1 is not in R = {0}, so
the theorem fails. This shows qPilotOutput_mem is load-bearing and is exactly
the hidden C1 membership.

A second model: keep qPilotOutput_mem but choose h enormous; then qLog <= h
holds trivially, while qLog has no relation to -|log q|. This shows hull_upper
and the arbitrary h make the conclusion vacuous relative to source.

## 5. Is C1 derived only from the three assumptions?

No. The exact dependency graph is:

    qPilotOutput_mem (field) + R_eq (definition) + qLog_eq (definition)
    + hull_upper (abstract bound) => qLog <= h.

The three source assumptions (Theorem3.11, Proposition3.9, Remark3.9.5) do
not supply qPilotOutput_mem; that is C1/xi-f. They also do not supply the
identifications qLog=Q and h=-|log Theta|, nor the source logVol/hull
structures. Therefore:

  - C1 is not derived from the three; it is assumed in the structure.
  - The "Theorem311Full" name is misleading: the structure includes the
    q-pilot possible-output membership, which is the missing xi-f/C1 content.
  - The global axiom sourceThreeAssumptions hides all fields; the theorem is
    conditional on that axiom, not unconditional over IUT initial Theta-data.

## 6. Exact hidden/extra condition list

H1. qPilotOutput_mem in Theorem311Full: q-pilot possible-output membership =
    C1/xi-f. This is the primary hidden condition.
H2. qPilotOutput arbitrary selection: no source proves the q-pilot input is an
    output; the selected output is not constructed from Theorem3.11.
H3. logVol arbitrary: no procession normalization, additivity, Ind1/2
    invariance, Ind3 upper-semi-compatibility, or log-shell structure.
H4. qLog_eq: qLog is defined as logVol of qPilotOutput, not the source
    q-pilot value; no Q=-|log q| identification.
H5. Remark395.h arbitrary: no hull, no -|log Theta|, no Ind.
H6. hull_upper arbitrary upper bound: not derived from Remark3.9.5 as stated.
H7. sourceThreeAssumptions axiom: asserts existence of the whole package;
    theorem depends on it.
H8. No identification R=R_{<=-|log Theta|}; R is just the logVol image.

## 7. Verdict

REJECT the claim that C1 follows from the three source assumptions without
hidden conditions. The theorem is a tautology whose key membership
(qPilotOutput_mem) is C1/xi-f inserted as a field. The structure also uses
arbitrary Output/logVol/h and a global existence axiom, and does not identify
qLog with Q or h with -|log Theta|. This is not a proof of Cor3.12 or C1; it is
a formalization of the conditional statement "if the q-pilot is a possible
output and every possible log-volume is bounded by h, then qLog<=h", with the
source objects replaced by abstract variables.

No Lean edits were made to the source file; this is a review only. No mixed/E3;
target_accepted=false; C1/P6 open.

## 8. Acceptance

Only C9-REVIEW-THREE-MULTI-20261025.md written. Review only; no edits to
source Lean except volumedet's own new file (none made by this task); no
mixed/E3; no independent kernel/comparator run. target_accepted=false.
