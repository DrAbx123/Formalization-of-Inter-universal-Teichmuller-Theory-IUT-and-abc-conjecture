# C3 — Source pilot region: SHEAF stage-1 record

Task ID / group / owner / date: C3 / N8 closure / primespine / 2026-10-22
Goal node / SHEAF stage: C3 SourcePilotRegion / stage 1 only.
Files: write tmp/sheaf/n8/closure/C3-STAGE1.md (this file). No Lean file is written or changed.
Integration/build owner: C3 owner; C10 integrator later. Build not applicable.
Shared interfaces/conflicts: C0 allowed input l,V,I : OriginalInput; C1 actual place/completion binding (to define); C2 local log/Kummer (to define). Do not edit C0/C1/C2 files. C3 consumers are C4, C9, C10.
Continuation: after stage-1 review, C3 stage 2 statement for one actual finite place and the q/theta-pilot to tensor-region interface; C1/C2 stage 2 remain separate nodes.
Acceptance: stage-1 record only; no Lean compile, no proof claim.

## 1. Mathematical target (objects, quantifiers, hypotheses)

For each allowed input

    l : PrimeGeFive
    V : Type uv
    I : OriginalInput.{u, uv, upi, umon, ui} l V

and each actual finite-place/completion binding supplied by C1, and the actual
local log/Kummer data supplied by C2, construct the actual source q/theta-pilot
and its landing in the arithmetic tensor region.

1. Actual q in the completion field.
   For the selected finite place v (residue prime p, completion K_v), construct
   an actual element q_v : K_v with q_v nonzero and of negative valuation, i.e.
   an actual FinitePlaceQCandidate at v (or the corresponding actual local q
   parameter). q_v is not a Real scalar placed into the value monoid.

2. Actual theta-pilot / theta packet.
   Construct the actual finite theta packet and theta-pilot values from the same
   source input: thetaPacket : FiniteThetaPacket l with scale j =
   realThetaValue q j; the actual source realization at v (local value-monoid
   image), the theta-pilot point family at processions n : ThetaPilotCarrier l
   and signed labels j : SignedLabel l.value, and the possible-image family.
   The construction must be indexed by the same I, v and local data; not a fresh
   arbitrary packet.

3. Kummer representation.
   Construct the actual Kummer class/root-change representation of q_v and the
   theta values in the local field, compatible with the C2 local log/Kummer
   arrow. The representation must be tied to actual p-power roots/Kummer maps,
   not a free LabelledKummerIso, free bijection or arbitrary quotient.

4. Integer lattice and tensor-region landing.
   Construct the actual integer lattice and tensor-factor landing into
   (ArithmeticTensorTupleBlock places tuple)^x with actual local places/tuple,
   and prove the q/theta-pilot representation lands in the intended canonical
   tensor region (arithmeticTupleCanonicalHull / arithmeticTensorTupleLogRegion)
   or the corresponding actual unit region. The landing is a theorem about the
   constructed map, not a stored hull_cover field.

5. Root-change compatibility.
   For the actual root/label changes and Kummer isomorphisms, prove the
   q/theta-pilot representation is compatible: changing roots/labels changes the
   local Kummer class by the actual action, and the tensor landing is preserved
   up to the actual action. No arbitrary equality between different witnesses.

6. Readout theorem.
   The norm, valuation and Real log readout of q_v are theorems:
       localSignedLog q_v = Real.log ||q_v||
       localLogMagnitude q_v = -localSignedLog q_v
       qNorm q_v = residueNormBase(place)^exponent
   and the theta log-scale identity from FiniteThetaPacket. The Real scalar is a
   readout of the actual local element, not the source object itself.

7. Source-to-tensor comparison.
   When actual comparison data exist, prove the q/theta-pilot generator lands in
   the source/arithmetic tensor region and its q-side normalized value is the
   actual q readout. This is the C3 input to C9; not a new free possibleImage,
   hdeg or hull_cover hypothesis.

Scope: nonarchimedean finite places. Archimedean q/theta data are a separate gap.

## 2. Paper anchors and route

- coord/N8-CLOSURE-ROUTE.md section 2 choice two and section 4 C3: actual
  q/theta-pilot, Kummer representation, tensor/region landing and root-change
  compatibility; consumers C4/C9.
- IUT III, Corollary 3.12 and proof (xi-d)-(xi-f): q-pilot log-volume, theta
  hull, possible log-volumes, log-Kummer correspondence in the 1-column.
- IUT III, Theorem 3.11(i)(ii): theta-pilot, Kummer isomorphisms and procession.
- IUT II, theta special values / finite theta packet.
- IUT IV local normalization is downstream; C3 fixes the local q/tensor-landing
  object, not the global volume normalization (C6/C8).

Route warning is binding: q is first an actual element in the completed local
field; the Real log-degree is a readout. The old full-hull/degree-faithful
bridge is only a conditional donor; A1 is not a proved Lean theorem.

## 3. Allowed input vs C3 must produce

### 3.1 Allowed input

1. C0: l, V, I : OriginalInput.
2. C1 (to define): actual place binding:
   - SourcePlaceRealization I;
   - actual finite place v, residue prime p, completion K_v, integers O_v;
   - C1 currently lists SourcePlaceRealization and strip-fiber comparison as
     gaps; no actual Lean type exists yet.
3. C2 (to define): actual local log/Kummer data:
   - actual unit log, kernel/image;
   - principal units;
   - actual Kummer arrow/root-change;
   - actual action descent.
   C2-STAGE1 records these as targets, not existing types.
4. Existing source data: actual theta packet/scale fields in source theaters and
   actual local value monoids/prime strip data.

### 3.2 C3 must produce

- Actual q_v : K_v (nonzero, valuation < 1), not a Real substitute.
- Actual theta packet and theta-pilot point/image family from the same source.
- Actual Kummer class/root representation of q_v/theta.
- Actual integer lattice and tensor-region landing map.
- Actual root-change compatibility laws.
- Readout theorems: norm/valuation/log and theta log-scale.
- Actual C3 package indexed by the same I/v/C1/C2 data.

### 3.3 Forbidden free data

C3 must not:
- put Real q directly into the value monoid or tensor as the source q;
- take a free FiniteThetaPacket with arbitrary q/scale;
- take a free SourceImageRealization (posRealAction/degree_of_q) as actual input;
- take free Kummer data, free Kummer class, free root system, free
  LabelledKummerIso or an arbitrary quotient;
- take free tensor landing/hull_cover/unit_bound or an arbitrary map from the
  tensor block to the source value carrier;
- use hdeg, degree-faithful, full-hull or sourceHullVolume < top as a source
  hypothesis;
- use SourceArithmeticThetaPilotBridge as an instance (conditional; no instance);
- use Nonempty, True, PUnit, arbitrary Equiv, arbitrary possibleImage or
  arbitrary set maps to replace actual q/theta/Kummer objects;
- treat A1 (q = 1/5 obstruction for SourceImageRealization) as a proved Lean
  theorem. It is a mathematical obstruction from group3 stage 1, not a Lean
  theorem, but it blocks unconditional use of R.

## 4. Existing Lean donors and exact limits

### 4.1 SourceImageHull (IUTIII Corollary312 StepXI)

Actual types/definitions:
- ThetaPilotCarrier l = Fin (lStar l + 1);
- ValueMonoidAt n m v = (I.primeStripAt n m).Mon v;
- thetaValueAt n m j = (I.theaterAt n m).thetaPacket.scale j;
- SourceImageRealization v:
      posRealAction : Multiplicative Real ->* I.ValueMonoidAt 0 0 v
      degree_of_q : I.logDegreeAt 0 0 v (posRealAction (ofAdd (log q))) = log q
  This is a hypothesis structure, not a constructed source realization;
- thetaImageValue R n j = R.posRealAction (thetaValueMonoidElement (n.1) 0 j);
- sourceThetaPilotPoint v R n j = fun _ => thetaImageValue R n j (constant on
  all components);
- sourceThetaPilotImageAt, PossibleThetaPilotImageAt, possibleThetaPilotImageSet;
- sourceHolomorphicHull v R n, sourceScalingUnits,
  sourceThetaPilotPoint_mem, sourceThetaPilotPoint_mem_sourceHolomorphicHull;
- LiteralArithmeticHullInterface and literalHullInterface_impossible record that
  the literal full arithmetic hull interface is impossible.

Limits: actual theta point depends on supplied R. No R is constructed in
SourceImageHull. The source packet q is Real; the source theta point is a
value-monoid image, not an arithmetic tensor unit. Full-hull interface impossible.

### 4.2 FiniteThetaPacket (IUTII/Theta)

Structure:
    q : Real
    q_pos : 0 < q
    scale : SignedLabel l.value -> Real
    scale_eq : forall j, scale j = realThetaValue q j.1
Proved: scale_pos, scale_ne_zero, scale_neg, log_scale, logVolume_eq_sum,
logVolume_ofQ, logVolume_neg_invariant.

Actual source packet shape for theta special values. Its q is Real, not a
completion element. Shape/source donor, not the C3 arithmetic q.

### 4.3 ArithmeticQPilot files (IUTIII/Corollary312)

Actual q-side objects:
- FinitePlaceQCandidate place:
      q : Completion place
      q_ne_zero : q != 0
      valuation_lt_one : v q < 1
  with exponent/order and positivity. Actual local q element type (q-parameter
  candidate; not a Tate uniformization claim).
- ArithmeticQPilotLogVolume:
      localSignedLog parameter = Real.log ||parameter.q||
      localLogMagnitude = -localSignedLog
  with qNorm_pos, qNorm_lt_one, localSignedLog_neg, localLogMagnitude_pos,
  unitNormLogDegree_q, pow laws.
- ArithmeticQPilotBaseChange:
      residueNormBase place = Ideal.absNorm place.maximalIdeal
      qNorm_eq_residueNormBase_zpow
      localLogMagnitude_eq_exponent_mul_log
      localSignedLog_map / qNorm_map / orderNormalizedMagnitude_map
  actual norm/valuation/readout formulas.
- ArithmeticQPilotGlobalNormalization:
      selected lower/upper places, fiber sums,
      absoluteDegreeNormalizedLowerSignedLog,
      absoluteDegreeNormalizedSignedLog_invariant, normalizedLowerSignedLog_neg.
  global normalization, downstream C6/C8, not C3 local construction.

Limits: actual local q element and readout, but no map from local q to source
theta value monoid, no Kummer class, no integer-lattice/tensor landing and no
root-change compatibility. There is no declaration named ArithmeticQPilot; it
is three namespaces.

### 4.4 SourceQSideComparison (IUTIII StepXI)

Actual definitions/theorems:
- sourceQSideNormalizedValue n j =
    card(SourceVolumeIndex l) * Real.log (thetaValueAt n 0 j);
- sourceSetVolume_possibleImage_eq_iSup_sourceQSide (needs hdeg);
- sourceSetVolume_possibleImage_ge_sourceQSide;
- sourceSetVolume_possibleImage_ge_ofReal_of_sourceQSide_le;
- sourceQSideNormalizedValue_neg_iff;
- sourceSetVolume_possibleImage_eq_zero_of_forall_theta_lt_one;
- iqHullCertificate_hqSlot_of_neg (ENNReal slot degenerates for q < 0);
- sourceUnitRegionHaarInterface_hqSlot_of_sourceQSide_le.

Limits: q-side numeric comparison layer. Substantive statements use hdeg
(forbidden as source hypothesis) and the ENNReal consumer slot is degenerate for
q < 0. No paper-faithful signed q carrier or actual q <= normalized theta
comparison constructed.

### 4.5 SourceArithmeticThetaPilotBridge (IUTIII StepXI)

Structure fields:
    toSource : (ArithmeticTensorTupleBlock places tuple)^x ->* I.ThetaPilotPoint v
    degreeMap : Additive (ArithmeticTensorTupleBlock places tuple)^x ->+ Real
    degree_compat : I.sourceLocalLogDegree v (toSource a) = degreeMap (Additive.ofMul a)
    thetaLift : SourceVolumeIndex l -> (ArithmeticTensorTupleBlock places tuple)^x
    theta_compat : toSource (thetaLift q) = sourceThetaPilotPoint v R q.1 q.2
    hull_cover : sourceHolomorphicHull v R n subset toSource '' (units in canonical hull)
    unit_bound : exists C, forall units in canonical hull, degreeMap <= C

Proved:
- sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge (from fields);
- no_degreeFaithful_fullHull_arithmeticThetaPilotBridge (F2 obstruction);
- not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful.

Limits: conditional comparison structure, not an instance. No fields constructed
from OriginalInput or tensor block. Under hdeg hull_cover impossible. Donor/
historical conditional theorem only, not C3 actual source construction.

### 4.6 Arithmetic tensor donors

- ArithmeticTensorTupleBlock = FinitePadicTensor of common prime completions;
- arithmeticTensorTupleLogRegion, compactness and one membership, exact
  tuple-projection image;
- arithmeticTupleCanonicalHull, canonical unit reference, canonical hull
  equality, compact canonical regions, positive finite measure;
- exists_arithmeticTensorTuple_fieldProduct: algebra equivalence to a finite
  product of complete ultrametric fields.

Limits: no unit-group equivalence A^x ≃* product (E j)^x declared, and no
valuation/norm map on the whole tensor algebra. Map A^x ->* I.ThetaPilotPoint v
cannot be assembled from these donors alone.

### 4.7 Kummer donors

- AbsoluteKummerInjection.absoluteKummerMap hmu : K^x ->* Hom(Gal(Kbar/K), mu_n);
- absoluteKummerMap_eq_one_iff: kernel = n-th powers;
- KummerGaloisClass.kummerRatioHom, KummerClass.kummerClass, rootSystemDiff.

Limits: abstract Galois-side Kummer layer; nothing feeds it into arithmetic tensor
block or source theta-pilot carrier. Group3 G3.6 records this bridge as missing.

## 5. Consumers

- C4: needs actual theta-pilot point/image family and local q/Kummer data to
  define source-witnessed output; C4 must not invent separate q/theta object.
- C9: needs actual local q value and normalized theta readout for q-side
  comparison and final Q <= Theta; C9 must not take q as free Real.
- C10: assembles C3 with C1/C2/C4-C9; C3 is actual q/theta-pilot source node,
  not a free parameter.
- C7 may use actual theta image/region once C3 supplies it; direct C3 consumers
  fixed by route are C4 and C9.

## 6. Statement dependencies

| Dependency | Declaration/file | Status |
|---|---|---|
| C0 allowed input | OriginalInput (SourceOriginalInput.lean:41) | exists |
| C1 actual place binding | SourcePlaceRealization / finite place + completion | to define; C1 gap |
| C2 local log/Kummer | SourceLogKummerData / actual Kummer arrow | to define; C2 gap |
| Source value monoid | ValueMonoidAt n m v | exists donor |
| Source theta packet | FiniteThetaPacket l | exists donor; q is Real |
| Source theta point | SourceImageRealization / sourceThetaPilotPoint | conditional; no R constructed |
| Source hull | sourceHolomorphicHull | exists donor, conditional on R |
| Actual local q element | FinitePlaceQCandidate place | exists donor |
| q readout | localSignedLog / localLogMagnitude / qNorm | exists donor |
| q base change/global norm | ArithmeticQPilotBaseChange / GlobalNormalization | exists donor |
| q-side comparison | sourceQSideNormalizedValue / conditional theorems | exists with hdeg; no paper-faithful q carrier |
| Tensor block | ArithmeticTensorTupleBlock | exists donor |
| Tensor log region/hull | arithmeticTensorTupleLogRegion / arithmeticTupleCanonicalHull | exists donor |
| Tensor field product | exists_arithmeticTensorTuple_fieldProduct | exists donor; no unit-group map |
| Conditional source-arithmetic bridge | ArithmeticThetaPilotBridge | exists conditional; no instance |
| Kummer layer | absoluteKummerMap etc. | exists abstract; no carrier bridge |

## 7. Proof dependencies (proved / conditional / gap)

Proved or existing:
- FiniteThetaPacket positivity/nonvanishing/log-scale/neg invariance;
- actual local q element and norm/valuation/log readout formulas;
- source theta point/image and hull membership theorems (conditional on R);
- tensor block/region/canonical hull compactness and finite measure;
- field-product algebra equivalence;
- conditional ArithmeticThetaPilotBridge consequences and hdeg no-go;
- q-side normalized value theorems (with hdeg where stated);
- Kummer map kernel theorem (abstract Galois side).

Conditional (not source-instantiated):
- SourceImageRealization and all sourceThetaPilotPoint/hull results depending on R;
- ArithmeticThetaPilotBridge fields;
- sourceHullVolume finiteness from the bridge.

Gap:
- C1 actual place/completion binding;
- actual q_v : K_v and its identification with source packet q (Real);
- actual theta-pilot construction from source data without unproved R;
- actual Kummer class/root-change tied to local field and tensor factors;
- integer lattice/tensor-region landing map and landing theorem;
- root-change compatibility laws;
- source-to-tensor comparison beyond conditional bridge;
- archimedean branch.

## 8. Natural-language proof steps

1. From C1, fix actual finite place v, completion K_v, integers O_v and prime p;
   from C2 fix actual local log/Kummer data at v.
2. Construct actual q_v : K_v (FinitePlaceQCandidate or equivalent) with q_v != 0
   and valuation < 1. Do not replace q_v by Real scalar.
3. Construct actual theta packet/values from the same source I/v/local data:
   FiniteThetaPacket with q/scale linked to actual theta special values; not a
   fresh arbitrary packet.
4. Construct actual source theta-pilot point family without assuming unproved
   SourceImageRealization; if a local value-monoid image is needed, build the
   scalar -> value-monoid map from actual local q/Kummer data, or record exact
   missing map. A1 says old R is not automatically instantiable; cannot assume.
5. Construct actual Kummer class/root representation of q_v/theta, using C2
   Kummer arrow and abstract Kummer donors where applicable; prove
   well-definedness and compatibility with log.
6. Construct integer lattice/tensor landing map from actual local places and
   tuple to ArithmeticTensorTupleBlock, and prove actual q/theta image lands in
   canonical region/hull. No stored hull_cover field.
7. Prove root-change compatibility laws for actual roots/labels/action.
8. Prove readout formulas: localSignedLog q_v = log ||q_v||, localLogMagnitude,
   qNorm = residueNormBase^exponent, theta log_scale.
9. When actual comparison data exists, prove generator-level normalized q-side
   value and hand to C9; no hdeg or full-hull bridge.
10. Assemble C3 object over C1/C2 data; record archimedean branch separately.

## 9. Exact gaps

G3.1 q-object mismatch. Source q in FiniteThetaPacket is Real; actual local q is
an element of Completion place. No declaration identifies Real.log source q with
localSignedLog arithmetic q. First concrete type gap. Only typeable comparison is
log(q_source) vs localSignedLog q_v, and it is not constructed.

G3.2 No map from arithmetic tensor block to source value monoid. Tensor units are
units of finite-dimensional Q_p-algebra; source carrier is N-fold product of a
commutative value monoid. No unit-group equivalence A^x ≃* product (E j)^x and no
valuation/norm map on A. Conditional ArithmeticThetaPilotBridge supplies such a
map only as a field.

G3.3 No actual Kummer class/root representation bridge. absoluteKummerMap and
rootSystemDiff live on abstract Galois side; nothing feeds them into local value
monoid or tensor block. C2 Kummer arrow is itself a to-define target.

G3.4 No root-change compatibility theorem for actual q/theta representation.
Source packet has scale_neg and log_scale, but no actual root/label action
compatibility with local Kummer class and tensor landing.

G3.5 SourceImageRealization conditional and A1 blocks unconditional use. No R
constructed. A1 records mathematical obstruction at concrete q = 1/5 source
theater; it is not a Lean theorem and must not be quoted as one, but C3 cannot
assume inhabited R. Actual theta-pilot must be constructed from actual local data
or exact missing map recorded.

G3.6 Full-hull/degree-faithful bridge impossible. no_degreeFaithful_fullHull and
not_nonempty_ArithmeticThetaPilotBridge_of_degreeFaithful are proved obstructions.
hdeg and full-hull cover are not source hypotheses; only generator-level,
non-degree-faithful route may be used.

G3.7 q-side comparison not paper-faithful. sourceQSideNormalizedValue uses
thetaValueAt and needs hdeg for exact volume statements; ENNReal hq slot is
degenerate for q < 0. No actual signed q carrier or q <= normalized theta
comparison constructed here.

G3.8 No integer-lattice/tensor landing theorem. Tensor block, log region and
canonical hull exist, but no actual q/theta-pilot map lands in them; conditional
bridge hull_cover is a field, not a theorem.

G3.9 C1/C2 dependencies absent. Without C1 actual place/completion binding and C2
actual local log/Kummer arrow, C3 cannot construct q_v or its Kummer
representation as source objects.

G3.10 Archimedean q/theta branch not formalized.

## 10. Stage-1 acceptance and stop

statement_compiles: not applicable (no Lean declaration in this stage).
proof_body_checked: not applicable.
kernel_closed: not applicable.
target_accepted: not applicable.

This record freezes C3 target, allowed input, produced objects, forbidden free
data, donor limits, C1/C2 dependencies, C4/C9/C10 consumers, q-object and
tensor-landing gaps, and status of old hdeg/full-hull conditional bridge and A1.
No Lean or production file is changed.

Stop after this stage-1 record. Next executable step is C3 stage 2: freeze exact
SourcePilotRegionData fields for one actual finite place (q_v in completion, theta
packet/point, Kummer representation, integer lattice/tensor landing, root-change
laws, readout) using C1/C2 actual data; do not assume SourceImageRealization or
fill the tensor map with a free field.
