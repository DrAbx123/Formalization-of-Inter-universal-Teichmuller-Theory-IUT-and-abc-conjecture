# Current path simplification audit

Date: 2026-10-29.  Scope: the new B-path files
`PaperSourceGeometryActual`, `PaperC3TensorGeometryActual`,
`PaperCompletionTensorActual`, plus the remaining paper/Theta-link path.

## Verdict

The new path is a **completion-valued, nondegenerate-index model**.  It removes
the two concrete defects (abstract `Mon` without a completion map, and constant
tensor places), but it still contains model-level simplifications that are not
proved equivalent to the frozen IUT source.  It is not yet the paper-level
path.

## S1. Value monoid replaced by completion units

`PaperSourceGeometryActual` defines

  CompletionValueCarrier place := (CommonPrimeCompletion place)^x,

and the value-to-completion map is `Units.coeHom`.  This is an actual map, but
it replaces the paper's abstract local value monoid `Mon v` by completion
units.  No theorem identifies the frozen `FPrimeStrip.Mon v` with this carrier.
Severity: high model change, not a theorem about the original source.

## S2. Degree normalization unverified

The new `completionValueDegree` is

  u |-> Multiplicative.ofAdd (Real.log ||u||)

using the `CommonPrimeCompletion` spectral norm.  No theorem proves this
equals the source prime-strip degree `(I.primeStripAt 0 0).degree v`, including
the paper degree normalization and any ramification factor.
Severity: high; this is the same norm-instance issue as the old `c_norm`
versus `localLogMagnitude` problem.

## S3. C3 tensor geometry is standalone

`PaperC3TensorGeometryActual` defines a new `PaperC3TensorGeometry` with

  tensorIndex := V
  tensorPlaceIndex v := Unit
  tensorPlaces v () := G.place v.

It is not an instance of the frozen `SourcePilotRegionData`.  `PaperPlaceComparison`
uses `indexEquiv := Equiv.refl V` and is tautological in this model; it does not
construct the existing `PrimeStripC3PlaceComparison` and does not supply the C3
q, thetaPacket, roots, kummerClass, tensorUnit or tensorLanding fields.
Severity: high; no actual C3/paper component is built yet.

## S4. Tensor factor shape simplified

`PaperCompletionTensorActual` uses one tensor factor per source place and
`tensorTuple v := ()`.  The paper's C3 tensor packet may have a nontrivial
`tensorPlaceIndex` and a prime-strip index not definitionally equal to `V`.
The current model has no proof that its tensor index/places are the paper C3
tensor index/places.
Severity: high.

## S5. Norm mismatch in tensor block

`PaperTensorBlock` is an `ArithmeticTensorTupleBlock` over
`CommonPrimeCompletion` (normalized spectral norm), while the value carrier
uses completion units with the default completion norm.  No theorem identifies
the two norms on the relevant q/theta elements.
Severity: high; exactly the earlier `QVFamNormInstanceGap` obstruction.

## S6. q, theta, Kummer, Ind, Theta-link absent

`PaperSourceGeometryActual` has only `place`; no actual `q`, `thetaPacket`,
`roots`, `kummerClass`, `tensorUnit`, `tensorLanding`.  There is no path yet
from this model to `ThetaLinkActual`, Ind1/2/3 compatibility, or the paper
multiradial comparison.
Severity: critical for paper-level xi-f.

## S7. Split reduction still a gap

`NativeSplitMultiplicativeAtLiftActual` reduces the split source field to
`CanonicalTateSplitReduction`, which is not proved.  `NativeSourceAssemblyFields`
is therefore still incomplete.
Severity: source assembly blocker, but not a shortcut.

## S8. Old concrete C3 still degenerate

`ConcreteC3DonorCompletionActual` still has constant `tensorPlaces` and
`tensorTuple := ()`.  The new model does not modify or replace the old concrete
C3 path.  The old concrete q=1/5 average target is also false.
Severity: old path excluded; do not use it as paper evidence.

## S9. Paper MU_log unit region placeholder

`PaperMuLogIQCarrierActual` packages the actual Haar `mu_log`, but the existing
interface has `unitRegion = canonicalHull` (R1 placeholder), not the paper
`lambda * O` unit region.  The Haar measure itself is actual; the full paper
unit-region normalization is not realized.
Severity: medium-high for paper normalization.

## S10. Rejected shortcuts

The following are proved false or directionally wrong and must stay out:

- label-sum hull (`CorrectedHullCounterexampleActual`: false for q<1 and
  sum j^2 > 1);
- `sourceSetVolume` / `ENNReal.ofReal` negative-log truncation;
- hull enclosure as the signed comparison (gives the opposite direction);
- value-layer `logDegree` as paper `mu_log`.

## What the current path actually proves

It proves actual facts about a **new completion-valued model**: the value
carrier is completion units, the tensor index is the source place type, and
the tensor block is the corresponding arithmetic tensor block.  It does not
yet prove that this model is the paper's C3/tensor packet, and it does not
construct the paper Theta-link/multiradial comparison.

## Required next steps to remove the simplifications

1. Prove the completion-unit value carrier is the frozen `FPrimeStrip.Mon v`
   (or define a source field identifying them), including degree.
2. Extend `PaperC3TensorGeometry` with actual q/thetaPacket/roots/kummerClass/
   tensorUnit/tensorLanding and build an actual `SourcePilotRegionData`.
3. Prove tensor index/places equal the paper C3 index/places, not just `V` by
   definition.
4. Identify the completion and spectral norms on the q/theta elements, or
   reprove normalization in the completion-valued model.
5. Construct possible Theta images and the holomorphic hull in the actual tensor
   block, then actual Haar `mu_log`; prove the paper comparison.

No `sorry`, extra axiom, PUnit/True, or toy carrier is used in this audit.

## S11. `PaperSourceGeometryKummerActual` q is `Classical.choice`

The new completion-valued q is

  completionValueQ v :=
    candidateUnits (Classical.choice (finitePlaceQCandidate_nonempty (G.place v).val)).

This is an arbitrary chosen q-candidate, not a field of the source geometry and
not proved to be the paper q at `G.place v`.  The theta values and q-power
Kummer action are therefore actual operations on an arbitrary candidate, not
on the specified paper q.  This must be replaced by an actual q field (and its
norm/contraction data) before the completion-valued model can be used as the
paper q.

## S12. Two parallel new source models, no bridge

`PaperSourceGeometryActual` defines `CompletionValuedSourceGeometry` indexed by a
single `V` with one fixed rational prime `p`.  `PaperBadPlaceTensorGeometryActual`
defines a second `DependentCompletionValuedGeometry` indexed by
`Bad (nativePlaceSelection T)` with a *dependent* rational prime `qVFamTensorP b`
per bad place.  There is no theorem identifying these two models or their
places/values.  The current path therefore has two incompatible geometry
layers, not one paper source geometry.

## S13. Dependent-prime geometry is not an actual arithmetic tensor block

`PaperBadPlaceTensorGeometryData` stores

  tensorPlaces i _ : (p : Nat) x FinitePlaceAtPrime T.arithmetic.F p

with `p = qVFamTensorP T i`, so the rational prime varies with the bad place.
The production `ArithmeticTensorTupleBlock places tuple` requires a single
fixed prime `p` for all tensor factors.  Consequently the dependent-prime
bundle cannot be fed to `ArithmeticTensorTupleBlock`; there is no actual tensor
block in this file.  The correct global object for varying bad-place primes must
be a product/direct sum of per-prime blocks (or an explicitly constructed
mixed-prime carrier), not one `Q_p`-tensor block.  This is a structural
simplification, not a missing lemma.

## S14. `paperC3SourceData` pairs an arbitrary q with the source-theater theta packet

`PaperC3SourceDataActual.paperC3SourceData` sets

  q := paperC3Q = Classical.choice (finitePlaceQCandidate_nonempty (G.place v).val)
  thetaPacket := (sourceTheater l).thetaPacket.

The source-theater theta packet has its own fixed q (the source theater Gaussian q).
No theorem proves this q equals the norm/contraction of `paperC3Q` at `G.place v`.
Thus the C3 record pairs an arbitrary chosen completion q with a theta packet of
a different q.  This is a semantic inconsistency, not a proved C3 instance.

Also `roots`, `roots'`, `kummerClass`, `rootChange`, `tensorUnit` and
`tensorLanding` remain exact inputs; no inhabitant is constructed.

## S15. closure hull is not the paper lambda-O holomorphic hull

`PaperC3TensorBlockActual` defines

  paperThetaHull thetaUnit := closure (paperPossibleThetaImageSet thetaUnit),

and `paperPossibleThetaImageSet_subset_hull` is the trivial `subset_closure`.
The paper holomorphic hull is the smallest lambda-O region containing the image
(Remark 3.9.5), i.e. a scaling hull, not the topological closure of the finite
image set.  The exact `lambdaOScaling` gap records this.  The current hull is
therefore a different, generally smaller object.

## S16. UnitFamily is an arbitrary input

`UnitFamily := SignedLabel -> (v : V) -> valueCarrier G v`.
No map from the source theta packet/q to this family is constructed; the
`thetaUnit_source_actual` gap records it.  The image points are actual tensor
points of arbitrary completion units, not the source Theta-pilot possible images.

## S17. injectivity of the place family is not proved

`places_injective` is a gap in `PaperC3TensorSourceGap`.  If `G.place` is not
injective, distinct tensor factors may repeat the same completion place.  The
tensor block itself compiles, but it is not yet the paper's indexed place family
with distinct completion factors.

## S18. Theta exponent is missing the 2l-th root (catastrophic)

`PaperC3ThetaUnitSourceActual` defines

  thetaUnit j v = qUnit v ^ (gaussExponent j.1).toNat

i.e. `q^(j^2)`.  Paper Theta values are `q_v^(j^2)` with
`q_v = q^(1/(2l))`, determined up to mu_{2l}.  Unless `qUnit` is already the
2l-th root (which is not proved; it is an arbitrary `FinitePlaceQCandidate`
chosen by `Classical.choice`), the model theta value has the wrong local
exponent by a factor `2l`.  This changes the theta hull volume by `2l` and can
make the comparison true for the wrong reason or false.  Catastrophic.

## S19. q and thetaPacket can be unrelated

`ThetaUnitSourceData` requires an input equality

  qUnit_norm : ||qUnit v|| = thetaPacket.q.

This is not derived from the source geometry; `thetaPacket` is an independent
field.  If the two q's differ, the theta unit family and the image/hull are for
a q different from the q-pilot q.  The resulting inequality is then a statement
about two unrelated q's.  Catastrophic if used as paper xi-f.

## S20. Image/hull ignore Ind and Kummer orbits

`paperPossibleThetaImageSet` is the finite range of one pure-tensor point per
signed label.  It does not include the Ind1/Ind2/Ind3 orbits, Kummer
isomorphisms, or the possible-image union of the paper.  `paperThetaHull` is
only `closure(image)` and not the lambda-O scaling hull.  This makes the hull
too small and the comparison too weak; an inequality for it does not imply the
paper inequality.  Catastrophic for paper-level xi-f.

## S21. Degree/norm normalization can shift all log-volumes

`completionValueDegree` uses the spectral norm logarithm.  The paper degree is
the source prime-strip degree with its own normalization/weights.  No equality
is proved.  A mismatch by a local degree factor changes every local log-volume
and can turn the inequality into a different, unscaled statement.  Catastrophic.

## S22. dependent-p tensor packet is not a single Qp tensor block

Bad places have different residue primes.  `ArithmeticTensorTupleBlock` is a
single-`p` Qp-tensor.  The dependent-prime bundle cannot be that object; a
product of per-b blocks is required.  Any global Haar/mu_log on the wrong
carrier is not the paper product measure.  Catastrophic.

## S23. Torsion six-slot carrier mismatch

`NativeSourceTorsionGaps.torsionLabel` has type

  Multiplicative (A.curve.LTorsion l) -> Fin 6,

where `LTorsion l` has cardinality `l^2` for `l >= 5`.  A constant or
non-faithful label is a toy; the correct six-slot carrier (actual six-torsion /
roots-of-unity data) is not constructed.  This is a target-definition problem,
not a missing inequality proof.

## S24. Zero signed label included in Theta image (catastrophic)

`PaperC3TensorBlockActual` has `paperZeroLabel` and `paperZeroImagePoint = 1`
(actual).  The image set is the range over **all** `SignedLabel`, including the
zero label.  Therefore the image always contains `1`.  Any nonzero lambda-O
candidate containing the image must have ||lambda|| >= 1, hence contains O, and
the lambda-O hull collapses to O (actual candidate zero-label argument).  This
makes the Theta hull log zero/trivial.  Paper Theta values on the non-zero
labels are `q_v^(j^2)` for `j != 0`; the zero label is the q-pilot, not a Theta
possible image.  Including zero is a constant/label simplification with
disastrous semantic effect.

## S25. Extra 2l-th root on qVFamily q (catastrophic)

`qVFamily T b` is the actual clause-B **local** q_v parameter
(`FinitePlaceQCandidate`, valuation < 1).  The existing actual qVFam theta
packet uses `FiniteThetaPacket.ofQ ||qVFamily q||`, hence theta values are
`q_v^(j^2)` directly (see `QVFamThetaImageActual`).  No extra `2l`-th root is
needed.  `PaperC3ThetaRootActual` / `PaperThetaRootObstructionActual` / the
Kummer extension files instead take a `2l`-th root of `G.qUnit`, giving values
`q_v^(j^2/(2l))`, which are too small.  The path currently has two inconsistent
theta constants; one of them must be wrong.  For qVFamily the correct choice is
the direct `q_v^(j^2)` branch.

## S26. sourceTheater thetaPacket is a different q

`PaperC3SourceDataActual` sets `thetaPacket := (sourceTheater l).thetaPacket`,
while `paperC3Q` is built from an arbitrary completion candidate.  The actual
qVFamily packet is `sourceThetaPacketFromQ T b` (qside file), not the source
theater packet.  Mixing them changes the theta values by a different q.

## S27. Degree/weight constants not identified

`sourceDegreeNormalizationFactor = 1 / card(SourceVolumeIndex)` and
`nativeBadLocalWeight` are constructed, but no theorem identifies them with the
paper degree normalization/weights (including any `2l` or cardinality factors).
A wrong constant here shifts every log-volume.  This remains unproved.

## S28. Haar/unit-region normalization

`paperMuLogHaar` is the raw additive Haar log volume; the paper normalized
`mu_log` uses `arithmeticTupleNormalizedLogVolume` (subtract O log, divide by
finrank).  `paperLambdaOCandidateLog` uses the normalized one, while
`paperMuLogHaar` is raw.  Do not mix raw and normalized logs.  The unit region
is actual lambda*O, but the raw Haar scale is not fixed by the paper; only the
normalized quotient is canonical.

## PAPER CHECK: 2l is an indeterminacy, not an exponent denominator

IUT III, Corollary 3.12 proof, corpus lines 10310-10315 (Fig. 3.4):

  mu_{2l} acts on {q^(j^2)}_{j=1,...,l*} -> {1}.

So the paper Theta values are `q^(j^2)` for nonzero labels `j=1,...,l*`,
and `2l` occurs only as the group of roots-of-unity indeterminacies
`mu_{2l}` acting on those values.  It is **not** a 2l-th root of q in the
theta value.  Corpus lines 10330-10331 confirm the procession average is over
`j in F_l^x`, i.e. the zero label is excluded from the Theta image (the zero
label is the q-pilot identification, line 10347-10350).

Conclusion: `PaperC3ThetaRootActual`, `PaperThetaRootObstructionActual` and the
Kummer root extension take an extra 2l-th root that the paper does not take.
The correct branch is `q^(j^2)` (qVFamily local q_v) with a separate mu_{2l}
indeterminacy action.  These root files are therefore not the paper Theta
values and must not feed the hull comparison.
