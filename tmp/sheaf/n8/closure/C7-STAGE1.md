# C7 — Source holomorphic hull: SHEAF stage-1 record

Task ID / group / owner / date: C7 / N8 closure / primespine / 2026-10-22
Goal node / SHEAF stage: C7 SourceHolomorphicHull / stage 1 only.
Files: write tmp/sheaf/n8/closure/C7-STAGE1.md (this file). No Lean file is written or changed.
Integration/build owner: C7 owner; C8/C10 integrator later. Build not applicable to this document.
Shared interfaces/conflicts: C0 allowed input l,V,I : OriginalInput; C4 source-witnessed U; C5 algorithm compatibility; C6 normalized weights. Do not edit C0/C1/C2/C3/C4/C5/C6 files. C7 consumers are C8 and C10.
Continuation: after stage-1 review, C7 stage 2 statement for the actual local finite-nonarchimedean hull; archimedean/global branches are separate child nodes.
Acceptance: stage-1 record only; no Lean compile, no proof claim.

## 1. Mathematical target (objects, quantifiers, hypotheses)

C7 must construct the actual source-determined common holomorphic hull of the
C4 output family, not merely a bound for each individually chosen image.

For each allowed input

    l : PrimeGeFive
    V : Type uv
    I : OriginalInput.{u, uv, upi, umon, ui} l V

and actual data supplied by C1/C2/C3, C4, C5 and C6, construct a set/region

    H(I,n)  (or H(I,n,x) at the actual state index)

in the actual output/tensor carrier such that:

1. H contains every permitted image:
       for every permitted source choice c (C4) and every algorithm-valid
       realization from C5, eval(c) lies in H.
   This is a common containment for the whole permitted family, not a separate
   bound depending on c.

2. H is an actual λO-hull region:
       H = λ * O
   for an actual nonzero scaling vector λ and an actual unit/reference region O
   in the relevant local product/IQ carrier, in the source direction fixed by
   the paper's hull operation. The region must be determined by the actual
   source data (C4 U, C5 operations, C6 weights), not an arbitrary data field.

3. H has positive finite volume:
       0 < mu(H) and mu(H) < top
   for the actual Haar measure, in the appropriate local normalized convention
   from C6.

4. The actual q-pilot point belongs to H:
       qPilot(I,n) in H.
   This must be proved from the actual construction, not supplied as a field.

5. H is common and choice-independent:
   changing the internal C4 witness or the C5 permitted algorithm realization
   does not change H; H is the same region for all permitted images. No
   pointwise bound with a choice-dependent constant is accepted as this target.

6. The construction is source-determined:
   compactness, nonempty coordinate projections, nonzero λ components and the
   finite product decomposition are proved from the actual source/tensor data
   (C1/C2/C3/C4/C5/C6), not added as free hypotheses such as an arbitrary
   SourceCompactBound, hull_cover or unit_bound field.

Scope: this stage targets the local finite nonarchimedean product. The
archimedean factors and the global finite-support/all-places object are
separate, explicitly listed gaps, not silently included.

## 2. Paper anchors and route

- coord/N8-CLOSURE-ROUTE.md section 4 C7: upgrade "each image is bounded" to a
  common source-determined region containing the whole permitted image family;
  reuse LocalFieldProductHull; consumers C8/C10.
- IUT III Remark 3.9.5(i): the holomorphic hull is the smallest λ * O region
  containing the image family, with the relative-compactness clause and the
  whole-ambient fallback.
- IUT III Remark 3.9.5(ii): φ(P) = intersection of admissible H containing P,
  with the finite-log-volume qualifier.
- IUT III Remark 3.9.5(iii): log-volume sandwich and compact indeterminacy.
- IUT III Corollary 3.12: compactness of the 1,∘U_{j,vQ} plus the definition of
  log-volume gives finiteness of -|log(Theta)|.
- IUT IV Prop. 1.4(i) normalization used for the actual local volume; details
  are C6's responsibility.

## 3. Allowed input vs C7 must produce

### 3.1 Allowed input

- C0: l, V, I : OriginalInput.
- C1 (to define): actual places/completions and local value data.
- C2 (to define): actual log/Kummer data.
- C3 (to define): actual q/theta-pilot and tensor/local data.
- C4 (to define): actual source-witnessed output family U with its witness
  family C/eval. C4-STAGE1 records that only a candidate U is currently
  definable; the final constrained C is a C4 gap.
- C5 (to define): actual IPL/SHE/APT algorithm compatibility and permitted
  operation family. C5-STAGE1 records that this is not yet constructed.
- C6 (to define): actual normalized weights and volume conventions.
- Existing arithmetic/local data: ArithmeticTensorTupleBlock,
  arithmeticTupleCanonicalHull, arithmeticTupleCanonicalUnitReference, Haar
  measures, LocalFieldProductHull.

### 3.2 C7 must produce

- The actual U family from C4 and the permitted-image family from C5 (not a
  candidate label-only U).
- An actual identification of the relevant local tensor/IQ carrier with a
  finite product of proper normed local fields (or the exact product structure
  used by LocalFieldProductHull), including the integer/unit region O.
- Proof that the actual U/image family has compact closure, is nonempty, and has
  nonzero coordinate projections.
- The actual λO-hull H, its common containment of all permitted images, its
  positive finite volume, and qPilot membership.
- The normalized volume data handed to C8 (with C6 conventions).
- A separate statement of the archimedean/global branches.

### 3.3 Forbidden substitutions

C7 must not:
- take a per-choice bound C(c) and call it a common hull;
- assume SourceCompactBound, IsCompact (closure U), nonempty or coordinatewise
  nonzero as free hypotheses;
- take a free scaling vector λ, free unit region O, free hull, or free
  hull_cover/unit_bound field;
- use the whole ambient as H without proving the relative-compactness branch;
- use an arbitrary finite product equivalence or arbitrary Haar measure;
- use hdeg or the degree-faithful full-hull bridge; that regime has a proved
  obstruction (F2) and is not the paper route;
- use the value-monoid sourceHolomorphicHull as if it were the actual IQ/λO
  hull without a proved comparison;
- use Nonempty, True, PUnit, arbitrary Set, or arbitrary Real/ENNReal data.

## 4. Existing Lean donors and exact limits

### 4.1 LocalFieldProductHull (production donor)

Definitions:
- unitRegion = {x | forall i, ||x i|| <= 1};
- region lam = {x | forall i, ||x i|| <= ||lam i||};
- region_eq_mul_unitRegion (for nonzero lam);
- hull S = intersection of all nonzero-coordinate λ-regions containing S.

Proved:
- exists_coordinate_maxima: compact nonempty S has coordinate maxima;
- exists_least_region: for compact nonempty S with nonzero coordinate
  projections, there is a least nonzero λ-region containing S;
- exists_hull_eq_region: hypothesis IsCompact S, S.Nonempty, coordinatewise
  nonzero => exists lam, all nonzero and hull S = region lam;
- exists_hull_eq_region_of_isCompact_closure: same for IsCompact (closure S),
  S.Nonempty, coordinatewise nonzero;
- least_region_unique, least_region_eq_intersection, hull_region,
  hull_idempotent;
- isCompact_unitRegion / isCompact_region (finite product of proper fields);
- measure_region_lt_top, measure_region_pos;
- measure_hull_pos_lt_top: under finite index, proper spaces, finite-on-compacts
  and open-positive Haar measure, plus IsCompact (closure S), S.Nonempty and
  coordinatewise nonzero, gives 0 < mu (hull S) and mu (hull S) < top;
- hull_eq_univ_of_not_isCompact_closure: whole-ambient fallback;
- normalizedLogVolume and its scaling laws (unweighted local expression).

Limits: this is an abstract finite-product construction over a family of proper
normed fields. It does not provide:
- the actual identification of the source IQ/tensor carrier with such a product;
- the actual U family from C4 or the permitted-image family from C5;
- compactness/nonempty/coordinatewise nonzero of the actual images;
- the source qPilot membership;
- archimedean/global treatment;
- C6 weights or packet normalization.
Its hypotheses must be proved from source data, not assumed.

### 4.2 SourceImageHull (production donor)

- sourceHolomorphicHull v R n = holomorphicHull (sourceScalingUnits v)
  (possibleThetaPilotImageSet v R n), where holomorphicHull is the least
  scaling-stable submonoid (value-monoid level);
- possibleThetaPilotImage_subset_sourceHolomorphicHull (P subset phi(P));
- sourceHolomorphicHull_paper_properties (P1,P2,P3 for that value-level class);
- sourceThetaPilotPoint_mem_sourceHolomorphicHull: the actual theta point lies in
  this value-monoid hull;
- sourceThetaPilotPoint_mem: membership in possible-image set;
- LiteralArithmeticHullInterface + literalHullInterface_impossible: the literal
  full arithmetic hull interface is impossible.

Limits: sourceHolomorphicHull is a value-monoid scaling-stable hull, not the
actual IQ/λO region of LocalFieldProductHull. It depends on the supplied
SourceImageRealization R. Its "least scaling-stable submonoid" class is not the
paper's λO hull with the relative-compactness clause. Under degree faithfulness
it is unbounded (F2), so it cannot be identified with the paper hull.

### 4.3 SourceImageHullVolume (production donor)

- sourceLocalLogDegree and sourcePointVolume;
- sourceHullVolume = sourceSetVolume of sourceHolomorphicHull;
- sourceHullVolume_ge_imageVolume;
- SourceCompactBound (named hypothesis: bounded log-degree of images);
- sourceSetVolume_possibleImage_lt_top_of_compactBound (needs hdeg and
  SourceCompactBound);
- sourceHullVolume_lt_top_of_hullBound (named whole-hull log-degree bound);
- sourceHullVolume_lt_top_of_scaledRegionImage (hull contained in λ times a
  scaled unit region with a log-degree bound; the containment is a named
  missing input);
- sourceHolomorphicHull_logDegree_unbounded, sourceHullVolume_eq_top_of_degreeFaithful
  (F2 obstruction under hdeg).

Limits: all finiteness theorems here are conditional on a compactness/hull-bound
hypothesis and (where stated) hdeg. C7 must prove the actual compactness and
containment, not assume these. The F2 obstruction forbids the degree-faithful
full-hull identification.

### 4.4 C4/C5/C6 interfaces

- C4: actual source-witnessed U; only a candidate label-only U is currently
  definable and the final constrained C is a gap.
- C5: actual IPL/SHE/APT and permitted algorithm family; not constructed.
- C6: actual normalized weights/volumes; not constructed beyond local
  conventions.

Limits: C7 cannot produce the actual common hull until C4's U is actual and C5's
permitted family is actual; the current candidate U is not the paper's output.

## 5. Consumers

- C8: uses the actual hull/λO region, its positive finite volume and the qPilot
  membership to form the relative determinant/arithmetic degree normalization.
- C10: assembles C7 with C1-C6/C8/C9; C7 supplies the hull node, not a free
  hull/volume parameter.
- C9 may use the hull bound for the final Q <= Theta, but the route's direct C7
  consumer is C8/C10.

## 6. Statement dependencies

| Dependency | Declaration/file | Status |
|---|---|---|
| C0 allowed input | OriginalInput | exists |
| C1 actual places/completions | SourcePlaceRealization | to define; C1 gap |
| C2 actual log/Kummer | SourceLogKummerData | to define; C2 gap |
| C3 actual q/theta | SourcePilotRegionData | to define; C3 gap |
| C4 actual U family | SourceWitnessedOutputData | candidate only; gap |
| C5 actual algorithm compatibility | SourceAlgorithmCompatibilityData | to define; gap |
| C6 normalized weights/volume | PaperNormalizedVolumeData | to define; gap |
| Local product hull | LocalFieldProductHull | exists abstract donor |
| Value-level source hull | SourceImageHull.sourceHolomorphicHull | exists conditional on R |
| Source volume/finiteness | SourceImageHullVolume | exists conditional on bounds/hdeg |
| Actual tensor product structure | ArithmeticTensorTupleBlock + field product equivalence | exists donor; no unit/IQ comparison |
| Actual Haar measure | canonical regions measure | exists donor |

## 7. Proof dependencies (proved / conditional / gap)

Proved or existing:
- LocalFieldProductHull least λO region from compact closure, nonempty,
  coordinatewise nonzero; uniqueness/intersection properties;
- positive finite measure of the nondegenerate hull under the stated measure
  hypotheses;
- whole-ambient fallback for non-compact closure;
- sourceHolomorphicHull P subset φ(P), P1/P2/P3 at value level;
- sourceThetaPilotPoint membership in sourceHolomorphicHull and possible image;
- sourceHullVolume monotonicity and conditional finiteness;
- F2 no-go under hdeg (unbounded hull, volume top).

Conditional/abstract:
- all LocalFieldProductHull source applications;
- sourceHullVolume_lt_top_of_hullBound/scaledRegionImage;
- SourceCompactBound and the pointwise/hull log-degree bounds.

Gap:
- actual C4 U and C5 permitted family;
- actual source IQ/tensor carrier identification with a finite product;
- compactness/nonempty/nonzero-coordinate proofs of the actual image family;
- actual λO hull on the source carrier;
- actual qPilot membership in that λO hull;
- archimedean/global finite-support objects;
- C6 normalized volume instance.

## 8. Natural-language proof steps

1. From C4, fix the actual source-witnessed output family U with its witness
   family C/eval (not the label-only candidate).
2. From C5, fix the actual permitted algorithm operations and prove that the
   full permitted image family is contained in the C4 image family (or the
   exact same-source union).
3. From C6, fix the actual local normalized volume convention and the actual
   unit/reference region O.
4. Identify the relevant local tensor/IQ carrier with a finite product of proper
   normed local fields using the actual tensor-field decomposition; prove the
   integer/unit region O corresponds to unitRegion.
5. Prove the actual image family S has compact closure, is nonempty, and has
   nonzero projection in every coordinate, using actual source compactness,
   theta values and C4 witnesses. Do not assume SourceCompactBound.
6. Apply LocalFieldProductHull.exists_hull_eq_region_of_isCompact_closure to
   obtain λ with all coordinates nonzero and hull S = region λ.
7. Apply measure_hull_pos_lt_top to get 0 < mu(hull S) and mu(hull S) < top.
8. Prove every permitted image lies in the hull (subset_hull / leastness), so
   the containment is common, not per-choice.
9. Prove the actual qPilot point lies in S (or in the permitted image family),
   hence in the hull; do not use only sourceThetaPilotPoint_mem_sourceHolomorphicHull.
10. Hand the λO region, volume and qPilot membership to C8/C10; state
    archimedean/global branches separately.

## 9. Exact gaps

G7.1 C4 actual U absent. C4-STAGE1 has only a candidate U using SignedLabel
and sourceThetaPilotPoint; the final source-constrained C and map from source
Choice to the output carrier are missing. C7 cannot construct the actual hull
from a candidate.

G7.2 C5 permitted family absent. IPL/SHE/APT algorithm compatibility and the
permitted operation family are not constructed; without them "all permitted
images" is undefined.

G7.3 No actual carrier decomposition. LocalFieldProductHull is over an abstract
finite family of proper normed fields. There is no proved identification of the
source IQ/tensor carrier (and its integer lattice/unit region) with such a
product. ArithmeticTensorTupleBlock has a field-product algebra equivalence, but
no unit-group/IQ comparison; this is a concrete missing bridge.

G7.4 Compactness/nonempty/coordinatewise nonzero of actual U not proved. The
LocalFieldProductHull hypotheses are not available from OriginalInput. The tree
has only named SourceCompactBound/hull-bound hypotheses and an F2 obstruction
under hdeg. The actual compactness of 1,∘U_{j,vQ} must be proved from the source
IQ/log-shell structure, not assumed.

G7.5 Actual λO hull on the source carrier absent. sourceHolomorphicHull is a
value-monoid scaling-stable hull, not the LocalFieldProductHull λO region. No
theorem identifies them; under degree faithfulness F2 shows the value hull is
unbounded, so the identification cannot be unconditionally true.

G7.6 qPilot membership in the actual λO hull absent. Membership is known only
for sourceHolomorphicHull; it does not automatically transfer to the actual
λO/IQ hull without the missing comparison.

G7.7 Archimedean and global branches. LocalFieldProductHull is a finite product
of proper normed fields; archimedean factors and a global finite-support object
are not covered. The route requires separate treatment, not a finite
nonarchimedean product silently replacing the global object.

G7.8 Actual Haar measure/normalization instance. The measure hypotheses
(finite on compacts, open positive) and C6 normalization must be instantiated on
the actual carrier; this is not done.

G7.9 No source-to-arithmetic hull comparison. Even with a value-level hull and
an arithmetic product hull, the comparison map between them is missing; C7 must
not take it as a free hull_cover field.

## 10. Stage-1 acceptance and stop

statement_compiles: not applicable (no Lean declaration in this stage).
proof_body_checked: not applicable.
kernel_closed: not applicable.
target_accepted: not applicable.

This record freezes C7's common λO-hull target, its source-determined
requirements (common containment, positive finite volume, qPilot membership),
the LocalFieldProductHull/SourceImageHull/SourceImageHullVolume donor limits,
the C4/C5/C6 dependencies, C8/C10 consumers, and exact gaps. It explicitly
rejects per-choice bounds, free compactness/hull_cover/unit_bound hypotheses,
and the degree-faithful full-hull route. No Lean or production file is changed.

Stop after this stage-1 record. Next executable step is C7 stage 2: freeze the
actual SourceHolomorphicHullData for the local finite nonarchimedean product,
including the carrier-product identification, compactness/nonempty/nonzero
coordinate proofs and qPilot membership; keep archimedean/global as child nodes.
