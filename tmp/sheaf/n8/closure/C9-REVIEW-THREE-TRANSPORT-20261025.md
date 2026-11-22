# C9 review: Theorem311Full.qPilotOutput_mem semantic audit

Task: task-461. Date: 2026-10-25. Reviewer: transport.
Audit of C9Cor312ThreeAssumptions.lean against IUT III lines 9524-9561.
No Lean edits; no mixed/E3; no arbitrary. Only this file written.
target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9Cor312ThreeAssumptions.lean | 59 | E71F22D4FDD47FAA8DE1646713AF88BBCD72E2541CD8121824ABAE131E48F703 |
| sources/IUT-III.txt | 11456 | 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D |

Relevant IUT III lines:

- IPL/final evaluation: 9524-9561;
- xi-e/xi-f: 10682-10715.

## 1. The Lean declaration

C9Cor312ThreeAssumptions.lean:

    structure Theorem311Full where
      Output : Type
      possibleOutputs : Set Output
      logVol : Output -> R
      qPilotOutput : Output
      qPilotOutput_mem : qPilotOutput in possibleOutputs

    structure Prop39 ...
    structure Remark395 ...
    structure ThreeAssumptions where
      T311 : Theorem311Full
      P39 : Prop39 T311
      R395 : Remark395 T311

    theorem cor312 (A : ThreeAssumptions) : A.P39.qLog <= A.R395.h

    axiom sourceThreeAssumptions : ThreeAssumptions

    theorem cor312_unconditional :
      sourceThreeAssumptions.P39.qLog <= sourceThreeAssumptions.R395.h

## 2. Verdict

REJECT Theorem311Full.qPilotOutput_mem as "full Theorem 3.11."

The field encodes exactly the target membership

    q-pilot output log-volume in R

which is Cor 3.12 xi-e/xi-f, not an assertion of Theorem 3.11's IPL.

Theorem 3.11/IPL says the output data are linked to the fixed q-pilot input
prime-strip by full poly-isomorphisms; it does NOT say the q-pilot
rigidification is itself one of the possible output rigidifications.

Therefore:

- Theorem311Full is not "Theorem 3.11 full"; it is Theorem 3.11 plus the
  C1/xi-f membership assumption.
- ThreeAssumptions are not the three source assumptions; the first is
  strengthened.
- cor312 is a valid tautology once qPilotOutput_mem is assumed.
- cor312_unconditional is unconditional only relative to the axiom
  sourceThreeAssumptions, which encodes the conclusion. It is circular as a
  proof of C1/Cor 3.12.

## 3. Exact source: IPL and final evaluation

IUT III lines 9524-9561 (IPL):

    (Input prime-strip link (IPL)) This output data is constructed in such a
    way that it is linked/related, via full poly-isomorphisms of
    F^turnstile-times-mu-prime-strips induced by operations in the algorithm,
    to the input data prime-strip, i.e. the "coric"/"fixed" q-pilot
    F^turnstile-times-mu-prime-strip, equipped with its rigidifying
    arithmetic holomorphic structure.

The source continues: the linking isomorphisms of intermediate prime-strips
are given by composing

- inverses of the first two lower horizontal arrows of the diagram of
  Remark 3.10.2,
- the first vertical arrow (Kummer theory portion),
- the three upper horizontal arrows (evaluation map portion).

Then lines 9551-9561:

    the final evaluation map portion of this composite involves a construction
    of the Theta-pilot object up to certain indeterminacies [Ind1, Ind2, Ind3],
    which ... may be interpreted ... as a construction of the global realified
    Frobenioid portion of an F^turnstile-times-mu-prime-strip, together with
    various possibilities [corresponding to the indeterminacies] for the
    "further rigidification" determined by the pilot object.

Key points:

- The output is linked to the input q-pilot prime-strip; "linked" is not
  "identical to" or "an element of the output set."
- The final evaluation gives "various possibilities for the further
  rigidification" determined by the pilot object; this is a space of
  possibilities, not the assertion that the fixed q-pilot rigidification is
  one of the possible outputs.
- The q-pilot is the **input** (codomain) object; the output is the
  Theta-pilot construction up to Ind1/2/3.

Thus IPL alone does not imply qPilotOutput in possibleOutputs.

## 4. What would imply the membership?

The membership is the source's xi-e/xi-f:

- xi-e, lines 10682-10704: expressibility relative to the 1-column under the
  condition that the pilot-object log-volume be the fixed value -|log q|;
- xi-f, lines 10705-10715: the construction of output possibilities
  constitutes a construction of the input q-pilot log-volume "perhaps only up
  to some sort of approximation, as a result of various indeterminacies"; the
  inclusion -|log q| in R_{<= -|log Theta|} then follows formally.

This is precisely the target step of Cor 3.12. It is not Theorem 3.11.

## 5. Step-by-step audit

### Theorem311Full.qPilotOutput_mem — REJECT

This field is the xi-f/C1 membership in disguise. Renaming it as "full
Theorem 3.11" is a semantic overclaim. The source's IPL is a linking property,
not a membership theorem.

### Prop39 — CONDITIONAL ACCEPT

Given an output qPilotOutput with logVol, the q-pilot log-volume can be
defined as its log-volume. But in the source the q-pilot log-volume is defined
directly from the q-pilot object, not from a hypothetical output. The structure
is harmless only after the smuggling in Theorem311Full; it does not fix it.

### Remark395 — CONDITIONAL ACCEPT

R = logVol '' possibleOutputs and h as an upper bound is a reasonable
finite encoding of the source's R_{<=h}. Accept conditional on Theorem311Full
being the source object; it is not.

### ThreeAssumptions — REJECT as source

The first assumption is strengthened by qPilotOutput_mem. The other two are
conditional wrappers. Therefore the triple is not "Theorem 3.11 + Prop 3.9 +
Remark 3.9.5"; it is "Theorem 3.11 + C1/xi-f + Prop 3.9 + Remark 3.9.5."

### cor312 — ACCEPT as tautology

Given qPilotOutput_mem and hull_upper, cor312 correctly derives qLog <= h.
It is a formal unpacking, not a proof of Cor 3.12.

### axiom sourceThreeAssumptions — REJECT as source axiom

The axiom asserts a ThreeAssumptions whose first component already contains
the desired membership. cor312_unconditional is therefore conditional on an
axiom that encodes C1. #print axioms will list sourceThreeAssumptions; the
"unconditional" label is misleading.

## 6. Exact repair required

A faithful Lean interface would replace the membership field by a source IPL
relation, for example:

    qPilotInput : Input
    outputInputLink :
      forall D in possibleOutputs, LinkedByFullPolyIso D qPilotInput

and would NOT include qPilotOutput as an output with membership. Then
qPilotOutput_mem would have to be proved from a separate xi-f assumption, not
from Theorem 3.11.

If one wants a conditional theorem, it should be labeled:

    Theorem 3.11 (IPL only) + xi-f membership
      => Cor 3.12 / C1,

not "three source assumptions."

## 7. Conclusion

Theorem311Full.qPilotOutput_mem is REJECTED as a faithful encoding of full
Theorem 3.11. IUT III lines 9524-9561 give an IPL linking of output data to the
fixed q-pilot input and a final evaluation construction up to Ind1/2/3; they do
not assert that the q-pilot rigidification is one of the possible output
rigidifications. That membership is exactly xi-e/xi-f, i.e. the C1/Cor 3.12
target step, and its inclusion in the structure is semantic smuggling.

Consequently ThreeAssumptions, cor312_unconditional, and the axiom
sourceThreeAssumptions do not constitute an unconditional proof of C1.
No Lean edits, mixed/E3 profile, or arbitrary data were used.

target_accepted=false.
