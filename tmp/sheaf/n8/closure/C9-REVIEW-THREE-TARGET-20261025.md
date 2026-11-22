# C9 review: ThreeAssumptions target / Cor3.12 statement audit

Task: task-467. Reviewer: qside. Date: 2026-10-25.
Review only; no edits to source Lean or to C9Cor312ThreeAssumptions.lean;
no mixed/E3; only this file written.

## 0. Reviewed file

tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean
SHA256 E71F22D4FDD47FAA8DE1646713AF88BBCD72E2541CD8121824ABAE131E48F703.

Read-only compile:
  lake env lean -j1 -R D:/lean tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean
  EXIT=0
  #print axioms cor312_unconditional
  => [propext, Classical.choice, Quot.sound, sourceThreeAssumptions]

No sorry.  But the file introduces a custom axiom and bakes C1 into its
definition of the three assumptions.

## 1. Verdict

REJECT:
- Theorem311Full as A1 = Theorem 3.11: it contains qPilotOutput and
  qPilotOutput_mem : qPilotOutput in possibleOutputs.  This is exactly C1
  (the q-pilot is an output), not a source theorem.
- Prop39 as independent A2: qLog = logVol qPilotOutput depends on the
  smuggled q-pilot output; source Prop3.9 reads q-pilot log-volume as input.
- Remark395 as A3 = Remark3.9.5: h is an arbitrary upper bound of the
  possible-output log-volume set, not the hull log-volume; hull_upper is an
  assumption, not derived from hull containment/monotonicity.
- cor312 as a derivation of Cor3.12 from A1+A2+A3: it is a valid abstract
  lemma from the file structures, but those structures already contain C1
  and hull_upper.
- axiom sourceThreeAssumptions: a custom axiom, not a source theorem.
- cor312_unconditional: depends on the custom axiom; not unconditional.
- Target qLog <= h as the Cor3.12 statement: it lacks -|log Theta|,
  -|log q|, the hull log-volume, and the normalization/T_can translation.

ACCEPT:
- The abstract kernel implication from the file own structures.
- The compile and #print axioms output as audit evidence.
- The inequality shape only as a conditional skeleton.

## 2. Line audit

### Theorem311Full, lines 13-18

Fields: Output, possibleOutputs, logVol, qPilotOutput, qPilotOutput_mem.
The field qPilotOutput_mem is C1.  Theorem 3.11 says the q-pilot is the fixed
input and the possible output data are linked to it by full
F^value x mu-prime-strip poly-isomorphisms.  It does not say the q-pilot input
is itself a possible output rigidification.  Putting that membership in A1 is
circular relative to the target.

There is also a type-level issue: qPilotOutput is an element of the abstract
Output type, while the source q-pilot is an object of the global realified
Frobenioid/prime-strip category.  No fiber/realification identification is
given.

### Prop39, lines 21-23

qLog = logVol qPilotOutput.  This is meaningful only after the smuggled
q-pilot-output field.  Proposition 3.9 defines the normalized q-pilot
log-volume as the input pilot log-volume; it does not identify the q-pilot
with an output element.  Reject as independent A2; accept only conditionally
on the smuggled structure.

### Remark395, lines 27-31

R = logVol image possibleOutputs.  h is an arbitrary real with
hull_upper : forall x in R, x <= h.  This does not define h as the log-volume
of the holomorphic hull.  Remark3.9.5 gives the hull and its log-volume; the
inequality for every possible output follows only from hull containment plus
log-volume monotonicity.  Neither containment nor monotonicity is formalized.
So hull_upper is an extra assumption, not A3.  The conclusion qLog<=h is an
abstract upper-bound fact, not the source inequality.

### ThreeAssumptions, lines 34-37

It packages the smuggled C1 and the extra hull_upper assumption as the three
source assumptions.  It is not equivalent to A1/A2/A3.

### theorem cor312, lines 41-45

Proof: qLog in R because qPilotOutput is in possibleOutputs; then hull_upper.
Valid for the file structures.  Reject as Cor3.12 derivation because C1 and
hull_upper are already assumed.

### axiom sourceThreeAssumptions, line 48

Custom axiom.  It is stronger than the intended source hypotheses and makes
cor312_unconditional vacuous as a proof of the source statement.

### cor312_unconditional, lines 51-53

Depends on sourceThreeAssumptions, as #print axioms shows.  Not unconditional
in the no-custom-axiom sense; and it proves only qLog<=h, not Cor3.12/P6.

### #print axioms, line 55

Useful and correct audit evidence: it exposes the custom axiom.  This is a
positive point of the file (honest print), but it confirms non-acceptance.

## 3. Target/Cor3.12 statement audit

The Lean target is:

    A.P39.qLog <= A.R395.h.

The Cor3.12 statement is:

    -|log(Theta)| in R,
    -|log(Theta)| >= -|log(q)|,

with -|log Theta| the procession-normalized log-volume of the holomorphic
hull of possible Theta-pilot images and -|log q| the q-pilot log-volume in the
same packet+procession normalization.

The Lean target lacks:
- Theta-pilot/hull object and possible-image union.
- The identification h = -|log Theta| and qLog = -|log q|.
- The q-pilot input/output distinction.
- The packet+procession normalization and T_can object identification.

Therefore qLog<=h is an abstract inequality template, not a formalization of
Cor3.12.  It can be used as a skeleton only after adding the missing objects.

## 4. Exact corrections needed (review only, not edits)

1. Remove qPilotOutput and qPilotOutput_mem from Theorem311Full; A1 should
   contain only source output data and links.
2. Add C1 as an explicit separate hypothesis:
   exists D0 in possibleOutputs with logVol D0 = qLog.
3. Define h as the log-volume of the holomorphic hull of possibleOutputs;
   prove hull_upper from hull containment and log-volume monotonicity, or
   keep it as a clearly named extra hypothesis, not A3.
4. Remove the axiom sourceThreeAssumptions; state the theorem conditional on
   ThreeAssumptions as a variable.
5. Rename cor312 to abstract_conditional unless the target is extended with
   -|log Theta|/-|log q| and T_can; the current statement is not Cor3.12.
6. For a paper-level target add qLog = -|log q|, h = -|log Theta|, and the
   normalization/T_can identification; otherwise keep it abstract.

## 5. Classification

COMPILED:
- EXIT=0, no sorry; cor312 is a valid abstract lemma from its structures.
- #print axioms correctly reports sourceThreeAssumptions.

REJECTED:
- Theorem311Full as A1 (contains C1).
- Prop39 as independent A2.
- Remark395 as A3 (h arbitrary upper bound; no hull definition).
- ThreeAssumptions as faithful source assumptions.
- cor312 as derivation of Cor3.12 from A1-A3.
- axiom sourceThreeAssumptions.
- cor312_unconditional as unconditional.
- qLog<=h as the Cor3.12 target statement.

ACCEPTED:
- Abstract kernel implication from the file structures.
- Compile/axiom evidence as audit information.
- Inequality shape as a conditional skeleton only.

## 6. Conclusion

The file is a valid abstract Lean exercise, but it does not faithfully
formalize Theorem3.11/Prop3.9/Remark3.9.5: it assumes C1 in A1
(qPilotOutput_mem), assumes an upper bound in A3 (hull_upper), adds a custom
axiom, and proves only an abstract inequality.  The target qLog<=h is not the
Cor3.12 statement.  It does NOT establish unconditional Cor3.12/P6 and should
be treated as a conditional skeleton/gap, not target accepted.

No source Lean or volumedet file was edited.  No mixed/E3.
target_accepted=false.

## 7. Sources

- tmp/sheaf/n8/closure/C9Cor312ThreeAssumptions.lean, SHA256
  E71F22D4FDD47FAA8DE1646713AF88BBCD72E2541CD8121824ABAE131E48F703;
  read-only compile EXIT=0; axioms include sourceThreeAssumptions.
- C9-COMPATIBILITY-LOCATION-20261025.md: C1 is not an A1-A3 consequence.
- C9-C1-DET-20261025.md: determinant degree does not imply C1.
- C9-C1-MASTER-20261025.md: A1+A2+A3 alone do not imply C1.
- IUT III Theorem3.11, Prop3.9, Remark3.9.5, Cor3.12:
  sources/IUT-III.txt SHA256
  822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.
