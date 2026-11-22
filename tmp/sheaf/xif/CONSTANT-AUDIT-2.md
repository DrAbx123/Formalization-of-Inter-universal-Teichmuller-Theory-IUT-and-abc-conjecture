# CONSTANT-AUDIT-2: xi-f numeric constants and provenance

Task: task-618. Scope: all 115 .lean files under tmp/sheaf/xif (paper/ and root).
Read-only except this report. No lake/compile.

## 1. Method

Scanned every .lean file under tmp/sheaf/xif for numeric literals in code
(excluding imports, set_option budgets, and comment text where possible), then
traced nontrivial literals to their declarations/theorems. Literals 0 and 1 occur
throughout generic arithmetic (add_zero, one_mul, Fin indices, positivity), so
they are classified generically rather than listed hundreds of times; every
nontrivial numeric literal found is listed below with the file:line evidence.

## 2. Verdict

No numeric literal is used as an unproven source theorem inside xi-f paper code.
The constants split into four classes:

A. actual definitions/theorems with proof;
B. actual concrete-model values (not general source values);
C. explicit conditional hypotheses / missing-bound definitions;
D. diagnostic counterexample constants, not assumptions.

The flagged constants are B, C, and D. In particular, 1/5 and 861 are
concrete-model/example values and must not be generalized to arbitrary l; 1/25
and 2 log 5 are conditional missing Tate bounds; 1/2 is a diagnostic Haar
rescaling counterexample, not a source normalization; the 10/5/2 array is the
concrete l = 5 signed-average computation, not a general identity.

## 3. Actual constants and provenance

### 3.1 0 and 1

Generic identities, Fin indices, positivity, and unit values. Evidence examples:
- tmp/sheaf/xif/paper/ThetaPacketContractionProof.lean:54-69 uses 0 and 1 for
  positivity/comparison;
- tmp/sheaf/xif/paper/XiFInequalityProof2.lean:64-107 uses 0/1 only in scalar
  inequality algebra.
No flag.

### 3.2 2

Actual rank/index arithmetic, not an arbitrary constant:
- Fin 2 index sets in SourceClauseC (torsion basis/GL2); e.g.
  tmp/sheaf/xif/paper/ThetaPacketQIdentificationActual.lean:83 (Fin 2 in audit
  context);
- Gauss exponent square j*j in FiniteThetaPacket; the literal 2 appears in
  index-rank formulas, not as an asserted numeric theorem.
No flag.

### 3.3 five / 1/5 / gaussianFiveThetaQ

Actual concrete-model constant, not a general source constant:
- LeanFormal/IUT/IUTI/HodgeTheater/ConcreteIntegralHodgeTheaterExample.lean:27-28
  defines gaussianFiveThetaQ as the norm of localQParameterFor 5;
- LeanFormal/IUT/IUTII/Frobenioid/Example36SourceTheaterCarrier.lean:177-186
  proves gaussianFiveThetaQ = (5:Real)^-1 and
  (sourceTheater l).thetaPacket.q = (5:Real)^-1;
- tmp/sheaf/xif/paper/ThetaPacketContractionProof.lean:54-69 and
  ThetaPacketQIdentificationActual.lean:83 reuse this theorem.
FLAG: concrete-model value. It is a proved example (not arbitrary), but it is
not the general source q parameter; paper files that use it for source-theater
constructions must not promote it to a universal q.

### 3.4 six / Fin 6

Source torsion/invariance slot, not a numeric theorem:
- SourceTorsionClause.torsionLabel : torsionCarrier -> Fin 6
  (LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:203-219);
- xi-f consumers use six-slot labels in PaperSignedHull/signed procession.
FLAG: this is a source field, not derived from ClauseC; task-533 already found
no construction from ClauseC. Six here is structural, not an arbitrary numeric
value, but its provenance is a source obligation.

### 3.5 card(SignedLabel l.value), lStar, 1/card

Actual definitions:
- SignedLabel is an integer-interval subtype with Fintype card l.value
  (LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean:94-98);
- lStar and card(SignedLabel)=l.value are actual definitions/theorems;
- uniform weights 1/card are actual procession weights
  (SignedHullNormalizationActual.procession_weight/weightTotal).
No flag.

### 3.6 sourceVolumeIndex card and 861 at l = 41

Actual formula, example-specific:
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHullVolume.lean:87-90
  proves card(SourceVolumeIndex l) = (lStar l.value + 1) * l.value;
- at l=41 this is 861, as cited in tmp/sheaf/xif/XiFContraction.lean:38,
  tmp/sheaf/xif/XiFHullVolume.lean:52, XiFQPilot.lean:36-37, XiFScaling.lean:16.
FLAG: 861 is the l=41 evaluation only; the general constant is the card formula,
not 861.

### 3.7 M = 1 normalization

Actual chosen normalization in SignedHullNormalizationActual:
- actualNormalizedHullData has tensorPower := 1
  (tmp/sheaf/xif/paper/SignedHullNormalizationActual.lean:222-235);
FLAG: this is a selected determinant normalization (M=1), not a source theorem
that M must be 1. It is proved actual within that normalization only.

## 4. Flagged conditional/missing constants

### 4.1 1/25 and 2 log 5

File: tmp/sheaf/xif/paper/NativeQNormActual.lean:73-99.
- NativeQTateNormBound : Prop is 2 * Real.log 5 <= nativeQLogMagnitude;
- NativeQNormLeTwentyFifth : Prop is nativeQNorm <= 1/25;
- conditional consumers nativeQLogMagnitude_ge_two_log_five and
  nativeQNorm_le_twentyFifth_of_normBound only consume these hypotheses.
FLAG: unproved conditional constants. They are not derived from the actual q
order/base residue norm; no theorem asserts them.

### 4.2 1/2 in unit-reference rescaling

File: tmp/sheaf/xif/paper/UnitReferenceNormalizationActual.lean:83-124.
- smallHaarScalar is ENNReal.ofReal((2 * unitReferenceMass)^-1);
- smallHaarScalar_unitReference_toReal proves the rescaled mass is 1/2;
- unitReferenceNormalization_fails_of_smallHaarScalar uses this to refute the
  universal target.
FLAG: diagnostic counterexample constant, not a source normalization or a
claim that the actual unit-reference mass is 1/2.

### 4.3 10/5/2 signed-average array

Files:
- tmp/sheaf/xif/paper/SignedAverageBoundActual.lean:19-23;
- tmp/sheaf/xif/paper/SignedAverageBoundQOneFifth.lean:21-24.
Content: for l=5 signed labels are -2,-1,0,1,2, exponent sum 10, card 5,
coefficient 2; hence signed average = 2 log 5, and the proposed bound
average <= log 5 is false.
FLAG: concrete l=5 arithmetic. The numbers 10/5/2 are proved arithmetic for
this model, but not a general identity; the proposed bound is explicitly not
asserted (and is false at l=5).

### 4.4 prose 4/5

File: tmp/sheaf/xif/paper/ThetaLinkActual.lean:311-324.
The text "conditional on 4/5" is a count of five obligation fields, not a
mathematical constant. No code literal 4/5 exists. No flag beyond prose clarity.

## 5. Constants checked and not flagged

- 0/1: generic arithmetic/positivity.
- 2: rank/index and Gaussian square.
- 5/1/5: concrete gaussianFiveThetaQ example (flagged as concrete only).
- 6: source Fin 6 torsion label (flagged as source structure).
- lStar, card(SignedLabel), 1/card: actual definitions/weights.
- 861: evaluation of actual card formula at l=41 (flagged as example only).
- M=1: selected normalization (flagged as selected only).
- 4/5 in ThetaLinkActual: prose count, not a literal.

## 6. Conclusion

No arbitrary numeric constant has been silently used as a source theorem in the
xi-f files. The constants that must not be generalized are:
1/5/gaussianFiveThetaQ (concrete source-theater example), 861 (l=41 special
evaluation), M=1 (chosen normalization), and the l=5 signed-average 10/5/2.
The unproved conditional constants are 1/25 and 2 log 5 (NativeQNormActual).
The 1/2 in UnitReferenceNormalizationActual is a diagnostic counterexample, not
an assumption. Prose "4/5" is an obligation count, not a numeric constant.

No lake; no proof changes; report only.
