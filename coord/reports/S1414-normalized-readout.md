# S1414: xi-f normalized readout transport (route C)

Date: 2026-10-31
Lean: `tmp/sheaf/xif/paper/S1414NormalizedReadoutActual.lean`
EXIT=0 (direct `lean -R D:\lean`, no sorry/admit/axiom declaration).
SHA256: `AB8B39CD3CD521A2D816107589ECCF69654BDCAC22BF794E1CC72EA168BEB64A`
Olean built: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1414NormalizedReadoutActual.olean`.

## 1. What is actually constructed

### 1.1 Isomorphism branch (source and reference region transported together)

* `s1414RelativeReadout μ S C = log (μ S).toReal - log (μ C).toReal`.
* `s1414RelativeReadout_image_eq`: for an actual `e : G ≃ₜ+ H`, Haar
  measures on both sides, compact closures and positive source masses,
  the relative readout of the pair `(e '' S, e '' C)` equals the source
  readout.  Proof is exactly `NormalizedHaarTransport.relative_log_mass_image_eq`.
* Concrete instance:
  `s1414QVFamBlockContinuousAddEquiv : qVFamTensorBlock T b ≃ₜ+ rootBase T b`
  from the actual one-factor `qVFamBlockLinearEquiv`;
  `s1414SourceReferenceIsomorphismTransport` transports the q[1u] region
  and the canonical reference region together and leaves the readout
  unchanged.

### 1.2 Intrinsic-measure branch (source uses the measure on the image)

* `s1414RelativeReadout_map_eq`: for an injective measurable map and
  measurable images, the pushforward Haar has the same relative readout:
  `readout (map f μ) (f '' S) (f '' C) = readout μ S C`.
* No ambient Haar = pushforward equality is asserted.  The pushforward is
  the actual `s1080PushforwardHaar = Measure.map rootStackEmbedding addHaar`;
  the ambient `rootStackHaar` is not used as a substitute.

### 1.3 Completion degree transport

* `s1414LowerDegreeNormalizedSignedLog`,
  `s1414UpperDegreeNormalizedSignedLog`: signed log norm divided by the
  absolute degree.
* `s1414CompletionDegreeReadoutTransport`: for `x != 0`,
  `-log||completionMap x|| / [K:Q]
     = (e*f / [K:k]) * (-log||x|| / [k:Q])`.
  Proof uses the actual `absoluteDegreeNormalizedLogNorm_completionMap`.
* `s1414CompletionDegreeReadoutInvariant`: dividing out `e*f/[K:k]`
  returns exactly the source readout.  This is the degree-normalized
  readout transport.

### 1.4 xi-f source/hull readout

* Reference region `s1414SourceReference =
  arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple`.
  Its compactness and positive finite Haar mass are actual
  (`isCompact_arithmeticTupleCanonicalRegions`,
  `measure_arithmeticTupleCanonicalRegions_pos_lt_top`).
* `s1414SourceReferenceImage = rootStackEmbedding '' s1414SourceReference`.
  It is compact (continuous image of compact) and therefore measurable;
  this is proved in-file (`s1414Embedding_continuous`,
  `s1414SourceReferenceImage_measurable`), not assumed.
* `s1414SourceReadout`: degree-normalized q[1u] readout relative to the
  reference; equal to `arithmeticTupleNormalizedLogVolume ... qPilotQ1URegion`.
* `s1414HullReadout`: degree-normalized pushforward readout of
  `rootStackPaperThetaHull` relative to `s1414SourceReferenceImage`.
* `s1414XiFNormalizedReadout_le`: the normalized inequality
  `s1414SourceReadout <= s1414HullReadout`, using the actual
  `s1086PerB_pushforward`, the pushforward mass identities for the hull
  and the reference image, and the monotonicity of the S1086 comparison.
* `s1414XiFNormalizedReadout_le_of_exact`: the same inequality with all
  non-source inputs discharged:
  - injectivity: `rootStackEmbedding_injective_actual` (actual);
  - embedding measurability: `s1414Embedding_measurable` (actual);
  - q[1u] positivity/finiteness: `s1091QPilotQ1U_measure_pos` /
    `s1091QPilotQ1U_measure_lt_top` (actual);
  - hull finiteness: `s1102Hull_finiteness_actual` (actual from the
    embedded measurability and the hull-image measurability).
  Only three exact source fields remain: the geometric containment, the
  q[1u] image measurability, and the product-lattice identification.

## 2. Exact first fields

The packaged structure is `S1414NormalizedReadoutData`; its fields are:

1. `sourceImageContainment : S1086Q1UImageContainment T b`
   (reduces to S1087's coefficient comparison `S1087CoeffLe`);
2. `q1uImageMeasurable : S1086Q1URegionMeasurable T b`;
3. `productImageEq : S1414ExactFirstField T b`, where
   `S1414ExactFirstField = S863ProductImageEq`;
4. `readout_le : s1414SourceReadout T b <= s1414HullReadout T b`.

The exact first field (the first field of the packaged transport) is the
geometric containment (`s1414NormalizedReadoutFirstField`).  The exact
first field of the measurability branch is `S863ProductImageEq`: the
product lattice `s839FractionalLattice * s839HolomorphicLattice` equals
the compact multiplication image `s863MulImage`.  Given it,
`s1414HullImageMeasurable_of_exactFirstField` proves compactness (hence
measurability) of `rootStackPaperThetaHull`.

The constructor `s1414NormalizedReadoutData_of_exact` builds the packaged
transport from exactly these three fields.  No field is filled with a
`Nonempty` carrier, a free function, or a `True` placeholder.

## 3. Axioms and scope

`#print axioms` on the main theorems reports only
`[propext, Classical.choice, Quot.sound]`.  There is no `sorry`, `admit`,
or declared `axiom`.

Not asserted / not used:

* ambient `rootStackHaar` = `s1080PushforwardHaar`;
* default norm = normalized/spectral norm;
* `S1086HaarEq` or any ambient-measure equality;
* `S1086Q1UImageContainment`, `S1086Q1URegionMeasurable`, or
  `S863ProductImageEq` unconditionally.

This is a local normalized-readout transport package.  It is not a
`target_accepted` closure: the three exact source fields above are still
open, and no Project build, comparator, or independent semantic review was
run.

## 4. Consumer / next step

Consumer: the xi-f paper chain
(`PaperXiFInclusion` / `S1086PerBQ1URootHullActual`).  The next concrete
action is to discharge `S863ProductImageEq` (product lattice = compact
multiplication image), then `S1086Q1UImageContainment` (S1087 coefficient
comparison), then `S1086Q1URegionMeasurable`.  Until then the packaged
transport remains conditional on those exact fields.
