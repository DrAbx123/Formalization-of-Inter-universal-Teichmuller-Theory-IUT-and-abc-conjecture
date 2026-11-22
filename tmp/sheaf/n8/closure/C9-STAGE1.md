# C9 stage 1: Values, boundedness and q-approximation

## Template fields

- Task ID / group / owner / date: N8-C9 / group5-6 integration / multiradial /
  2026-10-22.
- Goal node / SHEAF stage: C9 SourcePilotApproximation / stage 1.
- File: tmp/sheaf/n8/closure/C9-STAGE1.md (this file). No Lean file is written;
  no production file is edited.
- Integration/build owner: C10 integration owner (not this stage); build not
  applicable to this document.
- Shared interfaces/conflicts: C2/C3/C4/C5/C6/C7/C8 and C0-STAGE1. No shared
  definition changed here.
- Continuation: after stage 1 review, the C8 signed-readout/Values interface
  child, then C9 stage 2; do not add a free hq adapter.
- Acceptance: statement_compiles not applicable (no Lean declaration); proof
  body not checked; this record freezes objects/quantifiers/consumers/gaps.

## Target (paper)

IUT III Corollary 3.12 and proof Steps (xi-d)-(xi-f), text lines 10823-10898;
definition of -|log(Theta)| and -|log(q)| at 10324-10352.

The proof forms a collection of possible output data, takes the holomorphic
hull and the normalized log-volume, and shows that the allowed output log-volumes
are linked to -|log(q)|. The final inequality is obtained only after the
construction/approximation of the q-pilot value is established; it is not an
input.

C9 target, exactly as route section 4 C9:

~~~text
Values(I) : Set Real                 -- allowed output values from the same
                                     -- actual construction after C8
actual_values_bounded :
  forall v in Values(I), v <= Theta(I)
actual_q_approximated :
  forall epsilon > 0, exists v in Values(I), Q(I) - epsilon <= v
then Q(I) <= Theta(I)
~~~

C9 must NOT take any of the following as input:
- hq : Q(I) <= Theta(I) or any equivalent comparison;
- Values(I) := Set.Iic (Theta(I));
- Q(I) inserted into Values(I) by definition;
- a free qSigned/thetaSigned/targetSigned triple;
- the existing sourceXifSignedComparison hypothesis in place of a proof.

## Allowed input versus produced

Allowed input (C0-STAGE1.md): l, V, I : OriginalInput l V.

Produced inside the chain:
- C1: actual place v and SourceImageRealization R;
- C2: actual log/Kummer/K1-K2 data, including the q-side local data;
- C3: actual theta/q-pilot source data, thetaPilotCarrier n, SignedLabel j,
  sourceThetaPilotPoint/image/region, actual q-pilot value as far as C2/C3
  construct it;
- C4: actual witnessed output U(I,n,x) with dependent-pair witnesses (candidate
  Y = I.ThetaPilotPoint v; G4 primary);
- C5: same actual algorithm/IPL/SHE/APT operation correspondence;
- C6: actual normalization/weights/procession average;
- C7: actual common hull and finite positive volume;
- C8: actual relative determinant/degree and signed log-volume readout;
- C9: Values and the two source theorems;
- C10: assembly.

C9 does not re-introduce any produced object as input.

## Actual carriers available for the comparison

Existing source carriers (actual, already in the tree):

- sourceHullVolume : ENNReal
  (SourceImageHullVolume.lean:193)
- sourceRealHullVolume : Real := (sourceHullVolume).toReal
  (CertificateHullWiring.lean:247)
- sourceSignedHullLogVolume : Real := -sourceRealHullVolume
  (CardHullRealSignedLogVolume.lean:114)
- sourceSignedImageLogVolume : Real :=
    -(sourceSetVolume v (possibleThetaPilotImageSet v R n)).toReal
  (CardHullRealSignedLogVolume.lean:123; candidate q-side donor)
- SourceXifSignedComparison I v R n qSigned :=
    qSigned <= sourceSignedHullLogVolume v R n
  (CardHullRealSignedLogVolume.lean:198; currently a named hypothesis)
- sourceSignedHullCertificate / sourceSignedHullLinkEvidence /
  cor312OfSourceSignedHullComparison
  (CardHullRealSignedLogVolume.lean:399, :415, :435; the latter takes hq as
  input and is not C9's proof)
- sourceSetVolume / sourceSetVolume_mono / sourceHullVolume_ge_imageVolume /
  sourceSetVolume_possibleImage_eq / sourceSetVolume_possibleImage_ge_normalized
  (SourceImageHullVolume.lean:188, :197, :209, :220, :247)
- SourceCompactBound, sourceHullVolume_lt_top_of_compactBound,
  sourceHullVolume_lt_top_of_scaledRegionImage
  (SourceImageHullVolume.lean:264, :273, :318)
- SourceHullInterfaceDischarge: hull_logVolume_realRepresentation,
  ValueHullCompactnessInput, sourceHullVolume_lt_top_of_compactnessInput
  (SourceHullInterfaceDischarge.lean:85, :205, :223)
- sourceImageHullVolume / cardHullRealSignedLogVolume obligations: interface
  status, not a proof of the paper comparison.

These carriers define Theta(I) candidates:

~~~text
Theta(I) := sourceSignedHullLogVolume v R n
         = -sourceRealHullVolume v R n
~~~

in the finite branch. Q(I) is an actual q-pilot value to be constructed by
C2/C3/C8; sourceSignedImageLogVolume is only a donor/candidate for the q-side
readout, not by itself the actual Q(I) of the paper.

## Intended definition of Values(I)

Values(I) must be the set of allowed output values of the same actual
construction after C8, not a free image field.

Current structurally intended definition (stage-2 interface; C8 readout not yet
defined):

~~~text
Values(I) :=
  { y : Real |
      exists (n : ThetaPilotCarrier l)
             (x : I.ThetaPilotPoint v)
             (c : C4.C I n x),
        y = C8.signedLogVolumeReadout
              (C5.actualOutputOf (C4.eval I n x c)) }
~~~

Here:
- C4.C and C4.eval are the actual source-witnessed choice/eval (label-only
  candidate in C4 stage 1, full source-constrained C still G1);
- C5.actualOutputOf is the same actual algorithm output map, not a fresh
  set-theoretic function; C5 currently has only abstract Output and G0 missing
  strip/Output/Choice bridge;
- C8.signedLogVolumeReadout is the actual signed log-volume/degree readout after
  C6/C7/C8 normalization; C8 is not yet a landed type.

Consequently the definition above is the intended exact formula, but its RHS
types are not yet available. C9 does not replace them by arbitrary Real-valued
fields or by Set.Iic.

C8 must expose an interface of the following exact shape (stage-2 proposal):

~~~text
structure C8SignedValueReadout (I : OriginalInput l V) where
  OutputWitness : Type
  ofC4 : OutputWitness -> Sigma c, {y // C4.eval ... c = y}
  readout : OutputWitness -> Real
  readout_is_actual_signed_logVolume :
    forall w, readout w = <actual signed normalized log-volume of w>
  same_construction : forall w, <w is produced by the C2/C3/C5 algorithm>
~~~

No inhabitant of this structure is asserted here.

## actual_values_bounded

Statement:

~~~text
actual_values_bounded :
  forall y in Values(I), y <= Theta(I)
~~~

Natural-language route:

1. Take y in Values(I); by definition there is an actual output witness w with
   readout w = y.
2. C7 must prove the actual common hull contains the region represented by every
   allowed output witness from the same construction, not just one chosen output.
3. C8 readout must be monotone with respect to region containment for the
   signed normalized log-volume: if region(w) is contained in the hull, then
   readout(w) <= -sourceRealHullVolume (equivalently the corresponding
   signed/ENNReal inequality).
4. Combine 1-3 to obtain y <= Theta(I).
5. Use sourceSetVolume_mono / sourceHullVolume_ge_imageVolume
   (SourceImageHullVolume.lean:197, :209) only when the actual output region and
   the actual hull are connected; the generic monotonicity alone does not prove
   the algorithm's output is in the hull.

Proof dependencies: C4/C5 actual output witness and algorithm provenance; C7
common hull containment; C8 monotone signed readout; C6 normalization. Exact
gaps G1/G2 below.

## actual_q_approximated

Statement:

~~~text
actual_q_approximated :
  forall epsilon > 0, exists y in Values(I), Q(I) - epsilon <= y
~~~

Natural-language route:

1. Q(I) is the actual q-pilot signed log-volume constructed by C2/C3 (1-column
   log-Kummer; actual q element; C5 operation correspondence), not a free
   qSigned field.
2. The same algorithm must yield an allowed output value or an approximation
   sequence whose signed log-volume is within epsilon below Q(I). The paper
   allows approximation under indeterminacies (xi-f).
3. C8 readout translates that output value to Real; C7/C6 ensure the same
   normalization as Theta(I).
4. Hence there is y in Values(I) with Q(I) - epsilon <= y.

This is NOT a consequence of actual_values_bounded. It is a separate source
construction: C9 must prove it from C2/C3/C5 and the actual q-pilot/readout, not
assume it.

## Derivation of Q(I) <= Theta(I)

Assume Theta(I) < Q(I). Let epsilon = (Q(I) - Theta(I))/2 > 0.
By actual_q_approximated, choose y in Values(I) with
Q(I) - epsilon <= y.
By actual_values_bounded, y <= Theta(I).
Therefore Q(I) - epsilon <= Theta(I), i.e.
(Q(I) + Theta(I))/2 <= Theta(I), hence Q(I) <= Theta(I). Contradiction.
Thus not Theta(I) < Q(I), so Q(I) <= Theta(I).

The real proof is a standard linear-order argument; it is included here as the
final assembly and consumes only the two named theorems, not hq.

## Consumers

- C10 N8Assembly: consumes actual_values_bounded and actual_q_approximated and
  the Q <= Theta conclusion. It must not receive hq or free qSigned/thetaSigned.
- Downstream signed certificate: cor312OfSourceSignedHullComparison
  (CardHullRealSignedLogVolume.lean:435) currently takes hq as hypothesis. After
  C9 proves hq, it can be used as an adapter; it is not a C9 proof input.
- StepXIContract/FiniteStepXILinkEvidence: downstream contract types; qSigned/
  thetaSigned are currently free fields. C9 does not use them as source values.
- ABC bridge: downstream after C10; not part of C9.

## Statement dependencies

- C0-STAGE1.md: allowed input l, V, I : OriginalInput l V.
- C1: v, R (SourceImageRealization).
- C2: actual q-side local log/Kummer data and K1/K2.
- C3: actual q/theta-pilot, thetaPilotCarrier, SignedLabel, source theta point.
- C4-STAGE1.md: C/eval/U/witness (candidate; G4 primary).
- C5-STAGE1.md: same actual algorithm/IPL/SHE/APT interface and Output bridge
  (G0 missing).
- C6: normalization weights/procession average.
- C7: actual hull, common containment and finite positive volume.
- C8: actual determinant/degree and signed log-volume readout (not yet landed).
- Donors: SourceImageHullVolume, CertificateHullWiring, CardHullRealSignedLogVolume,
  SourceHullInterfaceDischarge.

## Proof dependencies

- sourceSetVolume_mono (SourceImageHullVolume.lean:197).
- sourceHullVolume_ge_imageVolume (:209).
- sourceSetVolume_possibleImage_eq (:220) and
  sourceSetVolume_possibleImage_ge_normalized (:247) for candidate theta side.
- sourceHullVolume_lt_top_of_compactBound (:273) / of_scaledRegionImage (:318)
  only under the actual common-bound hypothesis.
- sourceRealHullVolume = toReal sourceHullVolume
  (CertificateHullWiring.lean:247); sourceSignedHullLogVolume = negative
  (CardHullRealSignedLogVolume.lean:114).
- sourceXifSignedComparison (CardHullRealSignedLogVolume.lean:198) is the
  currently named residual, not a proof.
- No C2/C3/C8 actual q-readout proof exists yet.

## Reusable Mathlib / project donors

- Mathlib: Real linear order, epsilon argument, Set.range/Set.image, ENNReal
  toReal monotonicity, iSup lemmas.
- Project:
  - SourceImageHullVolume (sourceSetVolume/sourceHullVolume/monotonicity/
    compact bound).
  - CertificateHullWiring (sourceRealHullVolume, sourceRealHullVolume_le_theta,
    sourceRealHullVolume_ge_of_ofReal_le).
  - CardHullRealSignedLogVolume (signed hull/image volumes and the signed
    certificate).
  - SourceHullInterfaceDischarge (finite hull/compactness interfaces).
  - C0-C8 stage-1 records for the source construction and normalization.

## Exact gaps

G1. C8 signed readout / actual Values carrier is not defined. The intended
    Values formula needs C8.signedLogVolumeReadout and C5.actualOutputOf;
    neither type exists yet. No inhabitant of C8SignedValueReadout is asserted.
G2. actual_values_bounded needs C7 common hull containment for every allowed
    output and C8 monotonic signed readout; current monotonicity lemmas only
    give generic set containment, not the algorithm's output in the hull.
G3. actual_q_approximated is not implied by the bound. It needs actual q-pilot
    construction (C2/C3), same-algorithm output/approximation (C5), and C8
    readout; no such theorem currently exists.
G4. Q(I) actual q-pilot value is not a landed type. sourceSignedImageLogVolume
    is a candidate q-side donor, not the paper's q-pilot value; C2/C3 must
    construct Q(I) from the actual q and Kummer/log-Kummer data.
G5. Theta(I) finite branch: sourceHullVolume < top must be proved; the +inf
    branch is separate and cannot use toReal top = 0 as a finite value.
G6. Archimedean places are a separate branch: current SourceImageRealization
    and sourceHullVolume are the finite nonarchimedean development; archimedean
    q/theta data are C3 gap G6. Do not mix the two branches.
G7. Normalization/weight/procession-average/det tensor M are C6/C8 gaps; C9's
    bound and readout must use the same normalization as Theta(I), not a raw
    Haar log.
G8. Do not use hq, sourceXifSignedComparison, Set.Iic Theta, or Q inserted into
    Values as C9 input. These are the residuals C9 is supposed to eliminate.

## Archimedean and +inf branches (separate)

Archimedean:
- C3 records the archimedean q/theta data as a separate gap (group3 G6); the
  current sourceHullVolume/sourceImageRealization development is finite
  nonarchimedean.
- C9 finite nonarchimedean branch is first; archimedean needs a separate
  statement and may not be inferred from nonarchimedean by a generic toReal
  step.

+inf:
- Paper allows -|log(Theta)| in R union {+inf}; the proof has a trivial branch
  when -|log(Theta)| >= 0 (III:10354-10358), separate from the finite negative
  branch.
- sourceRealHullVolume = (sourceHullVolume).toReal and ENNReal.toReal top = 0;
  this maps the +inf branch to the wrong finite value 0. C9 must keep an
  extended/finite predicate and prove the +inf branch separately; it must not
  use toReal as the readout on the +inf branch.
- The finite branch needs sourceHullVolume < top or an actual bounded common
  hull; +inf cannot be silently treated as finite.

## Natural-language proof steps (target, not executed)

1. Fix C0 input l,V,I; take C1 v/R, C3 n/j/theta/q data, C2 q/Kummer data.
2. Define Theta(I) as the actual signed hull value in the finite branch; define
   Q(I) from the actual q-pilot construction.
3. Define Values(I) as the range of the C8 signed readout over the actual C4/C5
   output witnesses (same construction); not Set.Iic and not Q by definition.
4. Prove actual_values_bounded using C7 common hull containment and C8 monotone
   readout.
5. Prove actual_q_approximated using C2/C3 actual q and C5 same-algorithm
   output/approximation, read through C8.
6. Derive Q(I) <= Theta(I) by the epsilon argument above.
7. Separately handle the +inf branch and archimedean places; do not use toReal
   top = 0 or nonarchimedean data for archimedean.

Steps 2-5 are blocked by G1-G7.

## Stop boundary and status

- This stage writes no Lean declaration and does not modify production files.
- Values is defined here only as the intended formula over C4/C5/C8 actual
  construction; no arbitrary Real-valued readout is introduced.
- Stop after this stage-1 record. The next executable action is the C8
  signed-readout/Values interface child, then C9 stage 2; do not add a free hq
  adapter.

## Status fields

- statement_compiles: not applicable (no Lean declaration).
- proof_body_checked: not applicable / not run.
- kernel_closed: not applicable.
- target_accepted: not run.
- actual input: l, V, I : OriginalInput l V.
- Theta candidate: sourceSignedHullLogVolume v R n, finite branch.
- Q candidate source: C2/C3 actual q-pilot; sourceSignedImageLogVolume is a
  donor/candidate only.
- Values: intended range of C8 readout over C4/C5 output witnesses; exact type
  missing (G1).
- consumers: C10; downstream signed certificate only after C9 proves hq.
