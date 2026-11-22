# T11 STAGE 3 — theta value to completion (draft)

Task: supplement the actual `Real theta value -> CommonPrimeCompletion` map for
T11.  This is a proof draft plus single-file validation; no full build was run.

Files:
- `tmp/sheaf/n8/closure/ThetaValueCompletion.lean` (new draft)
- `tmp/sheaf/n8/closure/STAGE3.md` (this record)

## 1. Actual objects used

1. `thetaScale (C3) n j : Real` = `I.thetaValueAt (n.1 : Int) 0 j`
   (`SourceThetaToIQ.thetaScale`, definitional via `thetaScale_eq_theaterScale`).
2. `C3 : SourcePilotRegionData I` with actual fields:
   - `C3.qUnit : (CommonPrimeCompletion C3.place)ˣ`;
   - `C3.qUnit_eq : qUnit = candidateUnits C3.place C3.q`;
   - `C3.tensorLanding : CommonPrimeCompletion C3.place → ArithmeticTensorTupleBlock ...`;
   - `C3.thetaPacket : FiniteThetaPacket l`;
   - `C3.tensorLanding_q : tensorLanding q = tensorUnit`.
3. `FiniteThetaPacket.scale_eq : ∀ j, scale j = realThetaValue q j.1`;
   `FiniteThetaPacket.log_scale : Real.log (scale j) =
      (gaussExponent j.1).toNat * Real.log packet.q`.
4. `gaussExponent : Int → Nat` (lower theta kernel).
5. T11 interface `SourceThetaIQInterface C3` fields:
   `thetaCompletion : (n : ThetaPilotCarrier l) → SignedLabel l.value →
      CommonPrimeCompletion C3.place`,
   `thetaScale : ... → Real`, `thetaScale_eq`, `thetaImage : ... → IQCarrier C3`,
   `thetaImage_eq : thetaImage n j = C3.tensorLanding (thetaCompletion n j)`.

## 2. Draft construction

Because `qUnit` is the actual completion q-unit and the theta special value is
`q ^ gaussExponent j`, the draft uses the label-indexed completion candidate

```lean
thetaCompletionOfQUnit C3 n j :=
  ((C3.qUnit : CommonPrimeCompletion C3.place) : CommonPrimeCompletion C3.place) ^
    (gaussExponent j.1).toNat
```

This is exactly the q-unit read at the Gaussian exponent.  It uses `C3.qUnit`,
`gaussExponent`, and the actual completion; it does not use a product of fields.

Then `thetaIQInterfaceOfQUnit C3 : SourceThetaIQInterface C3` is constructed:
- `thetaCompletion := thetaCompletionOfQUnit C3`;
- `thetaScale := thetaScale C3`;
- `thetaScale_eq := rfl` (definitional from `I.thetaValueAt`);
- `thetaImage := fun n j => C3.tensorLanding (thetaCompletionOfQUnit C3 n j)`;
- `thetaImage_eq := rfl`.

The construction is a real candidate interface, not a new axiom or a free
field.  It does NOT claim a function `Real → CommonPrimeCompletion`.

## 3. thetaScale compatibility

`thetaScale_eq_packetScale` (named sorry, exact subnode T11a):

```lean
theorem thetaScale_eq_packetScale (C3) (n) (j) :
  thetaScale C3 n j = C3.thetaPacket.scale j
```

Once this identification is available, the real log compatibility is proved
without further sorry:

```lean
theorem thetaScale_log_eq_gauss (C3) (n) (j) :
  Real.log (thetaScale C3 n j) =
    (gaussExponent j.1).toNat * Real.log C3.thetaPacket.q := by
  rw [thetaScale_eq_packetScale C3 n j]
  exact C3.thetaPacket.log_scale j
```

This matches `gaussExponent` and `FiniteThetaPacket.scale_eq`; it proves the
real-log side of thetaScale compatibility.  It does not yet identify the
completion-side `qUnit` with `C3.thetaPacket.q`.

## 4. Exact missing subnodes

### T11a `thetaScale_eq_packetScale`
The source theta value `I.thetaValueAt n 0 j` must equal the finite packet
`C3.thetaPacket.scale j`.  The source scale is defined from the actual theater
theta packet, while `C3.thetaPacket` is a C3 field; no existing theorem links
them.  This is the named sorry in the draft.

### T11b real q ↔ completion q identification
`C3.thetaPacket.q : Real` and `C3.qUnit` lives in `CommonPrimeCompletion`.
There is no actual map `Real → CommonPrimeCompletion` and no existing
identification of the real q with the completion q.  The draft's
`thetaCompletionOfQUnit` is a label-indexed completion candidate, not a map
from the real value.  A full `Real theta value -> completion` map would need
an explicit source embedding `q : Real ↪ CommonPrimeCompletion` (or a source
theorem identifying `C3.thetaPacket.scale j` with `qUnit ^ exponent` under the
chosen completion).  No exact production type for this identification was
found; it is reported as an exact child obligation, not replaced by a free Map
or an arbitrary choice.

### T11c q ↔ thetaPacket identification
The q-side and theta-packet side are linked by T11a/T11b only conditionally;
no actual theorem identifies `C3.q` with `C3.thetaPacket.q` in the completion.
This is not hidden as a field.

## 5. Validation

- Single-file command: `pwsh -NoProfile -File D:/lean/tmp/n8-20261018/lead/lean-serial.ps1 env lean -j1 -R D:/lean tmp/sheaf/n8/closure/ThetaValueCompletion.lean`
- `EXIT 0`; actual sorry = 1 (`thetaScale_eq_packetScale`).
- No full build, no C10 assembly, no production edit.

## 6. Consumer / next

Consumer: `SourceThetaToIQ.thetaIQInterfaceOfQUnit` and T11's
`SourceThetaIQInterface`; C10 can use the constructed candidate interface only
after T11a/T11b are supplied.  Next concrete action: state T11b as a source
embedding/identification obligation with an exact type (or report that no such
type exists); do not introduce a free `Real → completion` map.


## 7. C4 value-monoid / T11 IQ alignment (C4IQAlignment.lean)

Artifacts:
- tmp/sheaf/n8/closure/C4IQAlignment.lean (draft; single-file exit 0)
- this section appended to the existing STAGE3 record; the earlier T11 completion
  draft above is preserved.

### 7.1 Exact comparison objects

C4 value layer:

~~~text
C4 : SourceWitnessedOutputData I Label
R  := C4.place.R : I.SourceImageRealization C4.place.v
thetaImageValue R n j : I.ValueMonoidAt 0 0 C4.place.v
sourceThetaPilotPoint v R n j : I.ThetaPilotPoint v
~~~

T11 IQ layer:

~~~text
C3 : SourcePilotRegionData I
IQCarrier C3 := C6IQCarrier C3.tensorPlaces C3.tensorTuple
              = ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple
thetaScale C3 n j : Real := I.thetaValueAt (n.1 : Int) 0 j
thetaImage : (n : ThetaPilotCarrier l) -> SignedLabel l.value -> IQCarrier C3
qPilotPoint : IQCarrier C3 = C3.tensorLanding (C3.q.q)
~~~

### 7.2 Actual alignment proved in the draft

The theta scale is the actual source scale and depends on n:

~~~text
thetaScale_eq_source_scale :
  thetaScale C3 n j =
    (I.theaterAt (n.1 : Int) 0).thetaPacket.scale j
~~~

Under source degree faithfulness at C4's C1 place,

~~~text
DegreeFaithful :=
  forall b : Real,
    I.logDegreeAt 0 0 C4.place.v
      (R.posRealAction (Multiplicative.ofAdd b)) = b
~~~

the common invariant is:

~~~text
thetaImageValue_logDegree_eq_log_thetaScale :
  I.logDegreeAt 0 0 C4.place.v (I.thetaImageValue R n j)
    = Real.log (thetaScale C3 n j)
~~~

Proof: thetaImageValue_eq_ofAdd_gauss, then DegreeFaithful, then
log_thetaValueAt_eq_gauss. This aligns log-degree, not values.

The conditional package Alignment (D : SourceThetaIQInterface C3) carries
DegreeFaithful, the scale identity, the log-degree identity, and membership of
D.thetaImage n j in image C3 D n. Alignment.ofDegreeFaithful constructs it.

### 7.3 Attempted actual map and obstruction

Required full map:

~~~text
ValueMonoidToIQMap (D) where
  toIQ : I.ValueMonoidAt 0 0 C4.place.v -> IQCarrier C3
  thetaImage_compat : forall n j,
    toIQ (I.thetaImageValue R n j) = D.thetaImage n j
~~~

ValueMonoidToIQObligation (D) := Nonempty (ValueMonoidToIQMap D). No inhabitant
is constructed.

Obstruction, in order of strength:
1. I.ValueMonoidAt 0 0 v is the abstract prime-strip monoid
   (I.primeStripAt 0 0).Mon v; IQCarrier C3 is a concrete finite-dimensional
   tensor of completions. No production declaration connects these types.
2. C3.tensorLanding accepts CommonPrimeCompletion, while the theta scale is
   Real. The tree has no Real-theta -> CommonPrimeCompletion map. The earlier
   T11 thetaCompletion interface is exactly this missing map.
3. SourceImageRealization supplies only posRealAction from Multiplicative Real;
   no inverse, surjectivity, or value-monoid equivalence is available. Theta
   values lie in its image, but an arbitrary value-monoid element need not.
4. The only invariant the two layers share is log-degree. Many tensor elements
   share a degree, so log-degree does not determine a carrier element; a map
   would need an additional actual embedding/choice not present.

No formal no-go theorem is proved. The draft reports the exact missing donor:

~~~text
ValueMonoidAt 0 0 C4.place.v -> CommonPrimeCompletion / IQCarrier C3
~~~

compatible with thetaImageValue R n j |-> D.thetaImage n j. The index-level map
(n,j) |-> D.thetaImage n j is not a map from C4 values and does not descend to
one (log_thetaValueAt_eq_gauss collapses n at log level).

### 7.4 Next exact statements

1. If a true value map is intended, supply the donor above; otherwise use the
   invariant surface
   logDegreeAt 0 0 v (thetaImageValue R n j) = Real.log (thetaScale C3 n j).
2. The T11 Real-theta -> completion map (thetaCompletion) remains the T11
   completion subnode; it cannot be derived from thetaScale alone.
3. Do not introduce a new C4 IQ proxy. C7 may use T11.image/qPilotPoint after
   the T11 completion gap is supplied; C4 remains an independent source witness.

### 7.5 Status

- C4IQAlignment.lean single-file compile: exit 0 (draft; no large build).
- Actual map constructed: no.
- Formal no-go proved: no; exact obstruction/missing donor recorded.
- Production edits: none.



## 8. C6/C8 actual unitReferenceLog bridge (appended 2026-10-23)

Artifact:
- tmp/sheaf/n8/closure/C6NormalizationProof.lean
- SHA256 5FA7CB671DFC966480EC72C3E842D57BC85FC8AA9CB30D1DD2CBEA9138797901
- 126 lines, no sorry
- lake env lean -R D:/lean tmp/sheaf/n8/closure/C6NormalizationProof.lean -> EXIT=0

This section is an appended research record. It does not change any stage-2
conclusion above.

### 8.1 Actual C6 unitReferenceLog

C6ActualIQData (tmp/sheaf/n8/closure/C6ActualIQData.lean) has the actual field

~~~text
unitReferenceLog : Real :=
  Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
~~~

where carrier = ArithmeticTensorTupleBlock places tuple, mu is the actual
additive Haar measure, and the canonical unit reference is the actual
production donor arithmeticTupleCanonicalUnitReference.

The C6 actual instance C6ActualIQData.actual sets this field to the same
expression. No product-of-fields data is involved.

### 8.2 Relations proved in C6NormalizationProof.lean

All statements are conditional only on exact field-identification hypotheses
for an arbitrary C6ActualIQData value. The actual instance satisfies them by
definition.

1) Normalized-volume formula with the actual unitReferenceLog:

~~~text
theorem normalizedLogVolume_eq_normalization_mul_log_ratio
  (hnorm : B.normalizedLogVolume =
    arithmeticTupleNormalizedLogVolume C3.tensorPlaces C3.tensorTuple mu)
  (hweight : B.normalizationWeight =
    1 / (Module.finrank ℚ_[C3.p]
      (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) : Real))
  (hunit : B.unitReferenceLog =
    Real.log (mu (arithmeticTupleCanonicalUnitReference
      C3.tensorPlaces C3.tensorTuple)).toReal)
  (S) :
  B.normalizedLogVolume S =
    B.normalizationWeight * (Real.log (mu S).toReal - B.unitReferenceLog)
~~~

2) On the C7 common hull (commonHull = B.hull):

~~~text
theorem normalizedLogVolume_commonHull_eq_weight_mul_signedHullLog_sub_unit
  (hnorm hweight hunit
   hhull : commonHull C3 mu B =
     arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple
   hsigned : B.signedHullLog =
     arithmeticTupleCanonicalHullHaarLog C3.tensorPlaces C3.tensorTuple mu) :
  B.normalizedLogVolume (commonHull C3 mu B) =
    B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog)
~~~

This conclusion is exactly the right-hand side of the corrected C8 target
(see 8.3), with the actual unitReferenceLog field.

3) Sign relation between the C8 iqMuLog (ENNReal.toReal) and the signed hull log:

~~~text
theorem iqMuLog_eq_max_signedHullLog
  (hlog : B.iqInterface.logVolume = haarLogVolume mu)
  (hhull : commonHull C3 mu B =
    arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple)
  (hsigned : B.signedHullLog =
    arithmeticTupleCanonicalHullHaarLog C3.tensorPlaces C3.tensorTuple mu)
  (hfin : mu (arithmeticTupleCanonicalHull
    C3.tensorPlaces C3.tensorTuple) < top) :
  iqMuLog = max B.signedHullLog 0
~~~

The ENNReal.toReal in iqMuLog is sign-blind; the unconditional equality
iqMuLog = signedHullLog is false. It holds only with 0 <= signedHullLog
(theorem iqMuLog_eq_signedHullLog_of_nonneg).

### 8.3 Corrected C8 target and proof route

Corrected C8 target in SourceDegreeComparisonIQ.lean:

~~~text
def iqDegree : Real := B.normalizedLogVolume (commonHull C3 mu B)
def iqSignedHullLog : Real := B.signedHullLog

theorem sourceDegreeComparisonIQ ... :
  iqDegree = B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog)
~~~

Proof route (no change to this statement):

1. Unfold iqDegree and commonHull. The goal becomes
   B.normalizedLogVolume (commonHull C3 mu B) =
     B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog).
2. Apply normalizedLogVolume_commonHull_eq_weight_mul_signedHullLog_sub_unit
   with hnorm/hweight/hunit/hhull/hsigned.
3. For B := C6ActualIQData.actual, hnorm/hweight/hunit/hhull/hsigned are
   definitional (rfl) because all five fields are defined by the same actual
   donors. No new stage-2 hypothesis is needed for the actual instance.
4. Do not replace signedHullLog by iqMuLog here. iqMuLog only gives
   max signedHullLog 0; the C8 target uses the signed value. If a future target
   uses iqMuLog, add a separate 0 <= signedHullLog hypothesis or prove it from
   the C7 hull logVolume_pos field.
5. The C4 -> IQ sourceImage bridge is still independent and not used by this
   equality; C8's hull is C7 commonHull = B.hull.

### 8.4 Remaining exact obligations

- For an arbitrary B : C6ActualIQData, hnorm/hweight/hunit/hhull/hsigned are
  explicit field-identification obligations. The structure currently does not
  carry proofs tying arbitrary values to the donors.
- The actual instance fields reduce by definition; a direct rfl-instantiated
  C8 theorem for C6ActualIQData.actual is the next proof step.
- No sign-blind replacement of signedHullLog is allowed.

### 8.5 Status

- C6NormalizationProof.lean: statement_compiles = true, EXIT=0; no sorry.
- proof_body_checked: the four conditional theorems above are checked by Lean.
- kernel_closed: not audited in this batch.
- target_accepted: no; C8 sourceDegreeComparisonIQ still has its named sorry.
- Stage-2 conclusions: unchanged.


## Actual donor search (append 2026-10-23)

The three component gaps are mapped to existing green donors below.  No new
Lean declaration is added in this pass; this is a stage-3 donor record only.

### SHE

- Shape donor: `SourceSHETransportLaws.SourceSimultaneousHolomorphicExpression`
  (`LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportLaws.lean:275`),
  with constructor `ofCommutingLegs` (`:299`).
- Gate constructor: `ofCommutingLegs` only builds the square from four supplied
  `FPrimeStripLink` legs and an equality of composites.
- Leg donor limitation: `I.fLinkAt` is a `FPrimeStripEquiv`, not a
  `FPrimeStripLink`; no `FPrimeStripEquiv -> FPrimeStripLink` constructor was
  found in `PrimeStripsConstruction.lean` or `PrimeStripCore.lean`.
- Could use `FPrimeStripLink.refl` for identity strips (gate only), but this is
  not the actual C2/C3 Kummer/localization square.
- Verdict: **no actual SHE square donor**.  The only green constructor is the
  gate instance; the four actual legs and their commutation equality remain the
  gap.

### APT

- One-column carrier donor: `sourceOneColumnStructureOfNumberField`
  (`LeanFormal/IUT/IUTIII/Theorem311/SourceArithmeticHolomorphicLanding.lean:434`),
  but its type is `SourceOneColumnArithmeticHolomorphicStructure
  (NumberField.FinitePlace k)`, not the C5 arbitrary `V`.  C1 supplies
  `V ≃ NumberFieldPlaceIndex`; no transport of the one-column structure along
  that equivalence is recorded.
- Landing predicate: `SourceLocalizationExpressible`
  (`SourceArithmeticHolomorphicLanding.lean:292`) with the green equivalence
  `... ↔ Nonempty Output` (`:298`) and concrete completion characterization
  `sourceLocalizationExpressible_completions_iff` (`:467`).  The latter still
  needs an actual arithmetic vector bundle, output datum, per-place reading and
  factorization; no such bundle exists in the tree.
- Algorithm donor: `finiteKernelSourceAlgorithm`
  (`LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialPresentationWiring.lean:473`)
  and `finiteKernelTwoColumnComparison` (`:590`).  These are actual finite
  kernel model instances, not the C4 output carrier `I.ThetaPilotPoint v`.
- Transport donor: `SourceAlgorithmicParallelTransport.reflexive`
  (`LeanFormal/IUT/IUTIII/Corollary312/StepXI/APT.lean:219`) requires the
  landing predicate; `SourceAPTSlotAssembly` (`:332`) is a consumer slot, not
  an instance.
- Procession donor: `SourceProcessionIsomorphism.refl 0`
  (`SourceAdjacentColumnProcessionIsomorphism.lean:190`) gives the identity
  adjacent-column gate only.
- Verdict: **no actual APT instance donor** for arbitrary C5 data.  The concrete
  finite-kernel algorithm and the completion one-column carrier are real but not
  connected to C4's `Y = I.ThetaPilotPoint v`.

### permitted signed-label family

- Label type donor: `SignedLabel l.value` (`Foundations/Theta/GaussianKernel.lean:94`),
  finite via `signedLabelFintype` (`:97`).
- Candidate finite-model packet: `ConcreteFiniteModel.thetaPacket`
  (`IUTIII/Theorem311/ConcreteFiniteModel.lean:298`) is indexed by all
  `SignedLabel l.value`; it gives no source-constrained subset.
- C4 candidate choice family is `SignedLabel l.value` with
  `sourceThetaPilotPoint` (`SourceWitnessedOutput.lean`), not a permitted set.
- No declaration named `permitted`/`pilotLabel`/source-choice family was found
  outside the C5 fields and the C4 candidate family.
- Verdict: **no actual permitted-family donor**; `actualPermittedFamily_exists`
  remains a genuine source-selection gap, not a packaging task.

### IPL

- Actual family donor now exists as `IPLFamilyData` (T10): `FPrimeStrip`,
  `FPrimeStripEquiv`, `permitted : Set (FPrimeStripEquiv source target)`,
  `allowed`.  This is the actual family-level IPL representation and does not
  use `Core/LinkSpan` as paper semantics.
- `SourcePolyIsoTransportLaws.polyIsoRel`
  (`SourcePolyIsoTransportLaws.lean:334`) remains the conditional kernel-level
  donor; it is not a substitute for `IPLFamilyData`.

## Revised next actions

1. SHE: search/construct `FPrimeStripEquiv -> FPrimeStripLink` bridge from the
   actual`I.fLinkAt` data; if absent, register a child gap rather than using
   identity links as the source square.
2. APT: need (a) transport of `sourceOneColumnStructureOfNumberField` along
   C1's place equivalence, and (b) a bridge from `finiteKernelSourceAlgorithm`
   output `ProcessionChoice l` to `I.ThetaPilotPoint v`; both are absent.
3. permitted: need an actual source-constrained subset of `SignedLabel l.value`
   and a chosen pilot label, not `Set.univ` or a singleton.
4. Keep `sourcePermittedFamily_exists`, `actualSHERepresentation_nonempty`,
   `actualAPTRepresentation_nonempty` as named component gaps until the donors
   above are constructed.

## Stage-1 child nodes

- C7-a theta-image containment: C7-a-theta-image-STAGE1.md
- C7-b IQ-hull log-volume positivity: C7-b-log-volume-positivity-STAGE1.md
- C7-c q-pilot membership: C7-c-qPilot-membership-STAGE1.md

These are stage-1 donor records only; the draft sorries remain proof placeholders,
not completion claims. First exact blocker remains C7-a.
