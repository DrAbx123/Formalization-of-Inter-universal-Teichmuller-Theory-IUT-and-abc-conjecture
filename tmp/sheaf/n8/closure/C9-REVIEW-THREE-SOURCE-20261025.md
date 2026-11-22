# C9 review: Prop39/Remark395 source fidelity

Task: task-466. Reviewer: kummer. Date: 2026-10-25.
Review only; no Lean edits; no mixed/E3. Only this file written.
target_accepted=false; P6 open.

## 0. Reviewed file

- tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean, 59 lines,
  SHA256 e71f22d4fdd47faa8de1646713af88bbcd72e2541cd8121824abae131e48f703.
- Source: IUT-III.txt, SHA256
  822e03da7e2a7402a3bb406d698bb3374401e3fb102058c80864d6c06139353d.
- Source passages: IPL Rem3.11.1(iii) lines 9524-9561; q-pilot coric/fixed
  lines 9509-9513 and 10166-10172; xi-b split lines 10582-10600;
  xi-d/e/f lines 10641-10715; Prop3.9; Remark3.9.5.

## 1. Verdict

REJECT as source-faithful and sufficient. The Lean theorem is valid relative
to its fields, but the load-bearing field qPilotOutput_mem is not a source
statement; it assumes the q-pilot input is one of the multiradial output
possibilities, which is exactly C1 and contradicts the source's distinction
between fixed q-pilot input and output possibilities.

The axiom sourceThreeAssumptions is not a source axiom; it encodes the desired
conclusion.

## 2. Field review

### 2.1 Theorem311Full (lines 10-19): REJECT

Fields: Output type; possibleOutputs; logVol; qPilotOutput; qPilotOutput_mem
(qPilotOutput in possibleOutputs).

Problems:

1. qPilotOutput_mem is not Theorem3.11. Source Rem3.11.1(iii) says output data
   are linked/related to the input q-pilot F^value x mu-prime-strip via full
   poly-isomorphisms. It does not say the q-pilot input is itself an output.
2. Source lines 10166-10172 and xi-a/b distinguish: -|log q| is the q-pilot
   image log-volume and the q-pilot is NOT regarded as subject to Ind1/2/3,
   while output possibilities ARE subject to Ind1/2/3. Identifying
   qPilotOutput with an element of possibleOutputs conflates the two.
3. Source has no canonical logVol function on arbitrary possible output
   regions before hull/procession normalization (xi-d). The field
   logVol : Output -> Real is an abstraction not present in Theorem3.11.
4. Source q-pilot is the object determined by q_v in the global realified
   Frobenioid (Def3.8(i)), not an element of the algorithm output set.

Thus Theorem311Full already contains C1 in qPilotOutput_mem.

### 2.2 Prop39 (lines 20-23): REJECT as source field

Fields qLog and qLog_eq : qLog = logVol qPilotOutput.

Source Prop3.9 gives the q-pilot log-volume, and qLog is its readout. If
qPilotOutput is the source q-pilot object, the equation is a tautological
definition, but the structure's qPilotOutput is an Output with membership in
possibleOutputs, so Prop39 inherits the unfaithful identification. The field
does not independently verify that the q-pilot log-volume is read on a
possible output; it is true only because the type already assumes it.

Verdict: not a faithful independent source field; conditional definition only.

### 2.3 Remark395 (lines 25-31): PARTIAL/REJECT as exact

Fields: R : Set Real; R_eq : R = logVol '' possibleOutputs; h : Real;
hull_upper : forall x in R, x <= h.

Problems:

1. Source R in xi-d-xi-f is the set of possible pilot-object log-volumes,
   not simply the image of an arbitrary logVol on output data. The source
   forms R after holomorphic hull, determinant/localization and normalized
   log-volume (lines 10641-10704); the Lean abstraction skips these.
2. hull_upper is a field, not a consequence of Prop3.9/Remark3.9.5 in the
   file. Source xi-f fixes h=-|log Theta| as the hull volume and possible
   log-volumes satisfy the inclusion in R_{<=h}; the Lean field asserts the
   upper bound rather than deriving it from hull monotonicity/Prop3.9.
3. h is unrelated to source normalization; it could be any upper bound.
   Source h is specifically the procession-normalized log-volume of the hull.

Verdict: acceptable abstract model of R bounded by h, not exact source
Remark3.9.5/xi-d.

### 2.4 sourceThreeAssumptions (lines 47-53): REJECT as source axiom

The file introduces axiom sourceThreeAssumptions : ThreeAssumptions and proves
cor312_unconditional from it. This is not a source axiom; it is a postulated
inhabitant of a structure whose fields already include C1. The printed axioms
of cor312_unconditional include sourceThreeAssumptions, so this is not an
unconditional source theorem.

## 3. Circularity

The proof uses qPilotOutput_mem to put qPilotOutput in possibleOutputs, qLog_eq
to identify qLog with its logVol, R_eq to put qLog in R, and hull_upper to
conclude qLog <= h. Step 1 is exactly the missing C1 existence/identification.
Therefore the argument is circular relative to the source: it assumes the
q-pilot output membership it is supposed to prove from IPL/Prop3.9/Remark3.9.5.

The Lean theorem is algebraically valid under the fields, but its source
interpretation is not.

## 4. What would be faithful

A faithful Theorem3.11 structure would have:

- a fixed q-pilot input object/rigidification QP_in with q-log-volume Q, not
  an element of possibleOutputs;
- output possibilities D with only their F^value-prime-strip link
  pi(D) ~ QP_in, plus Ind1/2/3 on the F^unit x mu side;
- a separate source theorem (xi-e/xi-f) that constructs Q as a possible output
  log-volume, with the source approximation caveat;
- R defined after hull/determinant/log-volume, not as an arbitrary image;
- hull_upper derived from hull monotonicity/Prop3.9, not assumed.

Without these, the Lean file does not formalize Prop3.9/Remark3.9.5; it
formalizes a conditional structure with C1 built in.

## 5. Classification

| item | status |
|---|---|
| conditional theorem qLog<=h under fields | VALID Lean-relative |
| Theorem311Full qPilotOutput_mem | NOT SOURCE; assumes C1 |
| q-pilot input in possibleOutputs | CONTRADICTS source distinction |
| Prop39 qLog_eq | conditional definition on unfaithful Output |
| Remark395 R_eq | abstraction, not source xi-d R |
| hull_upper | field assumption, not derived |
| sourceThreeAssumptions axiom | NOT source; circular |
| source fidelity Prop3.9/Rem3.9.5 | REJECT |
| sufficient for unconditional C1 | NO; circular |
| sufficient for conditional Lean theorem | YES relative to fields |

## 6. Conclusion

The ThreeAssumptions Lean file is a correct conditional abstraction but not a
faithful source rendering. Its key field qPilotOutput_mem assumes that the
q-pilot input is one of the multiradial output possibilities; source IPL only
links output to input, and the q-pilot is explicitly not subject to Ind1/2/3.
Prop39 inherits this conflation, Remark395's R/hull_upper are source-skipping
abstractions, and sourceThreeAssumptions is an axiom that encodes C1. The proof
is circular with respect to the source question. REJECT as
source-faithful/sufficient; ACCEPT only the Lean-relative conditional theorem
under its fields.

No Lean edits; no mixed/E3; no arbitrary source axiom; target_accepted=false;
P6 open.

## 7. Status

- Independent review only; no Lean/Project edits.
- Prop39/Remark395 fields rejected as source-faithful; qPilotOutput_mem is C1
  assumption, source distinction ignored.
- target_accepted=false.
