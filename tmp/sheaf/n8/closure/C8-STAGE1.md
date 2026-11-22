# C8 — Source degree comparison: SHEAF stage-1 record

Task ID / group / owner / date: C8 / N8 closure / primespine / 2026-10-22
Goal node / SHEAF stage: C8 SourceDegreeComparison / stage 1 only.
Files: write tmp/sheaf/n8/closure/C8-STAGE1.md (this file). No Lean file is written or changed.
Integration/build owner: C8 owner; C9/C10 integrator later. Build not applicable.
Shared interfaces/conflicts: C6 normalized weights/volume; C7 actual λO-hull; C0 allowed input; C1/C2/C3 actual source data. Do not edit C0-C7 files. C8 consumers are C9 and C10.
Continuation: after stage-1 review, C8 stage 2 statement for the local finite nonarchimedean relative determinant/degree equality; global product formula/archimedean/+inf are separate child nodes.
Acceptance: stage-1 record only; no Lean compile, no proof claim.

## 1. Mathematical target (objects, quantifiers, hypotheses)

C8 must construct the actual relative determinant and arithmetic
degree/log-volume equality for the C7 hull/arithmetic vector bundle, using the
C6 weights. It must not replace (Ob3-3) by a free field.

For each allowed input

    l : PrimeGeFive
    V : Type uv
    I : OriginalInput.{u, uv, upi, umon, ui} l V

and actual data from C1-C7, construct:

1. Actual arithmetic vector bundle/lattice.
   The actual C7 hull (a λO region in the local product/tensor carrier)
   determines an actual arithmetic vector bundle/lattice over the relevant
   local ring/Frobenioid, relative to the actual structure sheaf O. Build it
   from the C7 hull and actual tensor/lattice data, not from an arbitrary type.

2. Actual relative determinant.
   Construct the determinant line bundle of the arithmetic vector bundle
   relative to the structure-sheaf determinant:
       det(bundle) - det(O)
   in the actual line-bundle/Frobenioid carrier. The relative determinant, not
   only a real log-degree profile, is the object of (Ob3-1).

3. Actual weighted tensor powers.
   For the actual C6 weights/N_v/denominators, construct positive tensor powers
   of the determinants of the tensor-packet direct summands, with the
   structure-sheaf inverse determinant adjustment of (Ob3-1-2), and the actual
   positive integer M of (Ob3-2). M is determined by the actual weights (the
   N_E of Rmk 3.1.1(iv)), not a free structure field.

4. Actual det tensor M and its arithmetic degree.
   Construct det^⊗M on the actual arithmetic line bundle and its arithmetic
   degree. Prove M positive, the operation well-defined, and changing M by a
   permitted positive multiple leaves the normalized readout consistent
   (sufficient divisibility).

5. Arithmetic degree/log-volume equality (Ob3-3).
   Prove, for the actual objects and actual normalization factors,
       arithmetic degree of det^⊗M(bundle) relative to O
         = log-volume of the original arithmetic vector bundle
   in the normalization fixed by C6/IUT IV Prop. 1.4(i). Both sides must be
   independently constructed; the equality cannot define either side or be a
   free field.

6. Local/global scope.
   The local finite nonarchimedean relative determinant/degree statement is
   first. The global all-places arithmetic degree and product formula are a
   separate child; a local equality is not the global arithmetic degree.

7. +inf and archimedean branches are separate. The finite normalization
   identity does not handle the extended +inf branch or archimedean factors.

## 2. Paper anchors and route

- coord/N8-CLOSURE-ROUTE.md section 4 C8: actual relative determinant, tensor
  powers, global arithmetic degree/log-volume equality; M from actual weights;
  finite/infinite and product-formula separate.
- IUT III Remark 3.9.5(vii), (Ob1)-(Ob3-3), corpus 7875-7987:
  arithmetic line bundle / O_k-module; hull -> arithmetic vector bundle;
  determinant -> arithmetic line bundle; weighted tensor powers of determinants
  corresponding to N_v weights; inverse determinant of structure sheaf;
  det^⊗M with uniquely determined positive M; arithmetic degree interpreted as
  log-volume with suitable normalization factors.
- IUT IV Remark 1.7.1, corpus 1009-1054: normalized weights
  lambda_v = [(F_mod)_v:Q_vQ]; exponents need not be relatively prime; M
  sufficiently divisible.
- IUT IV Prop. 1.4(i): normalized log-volume divisor D = finrank_{Q_p}.
- IUT III Corollary 3.12 Step (xi-d): determinant + normalized log-volume and
  the q-pilot comparison.

## 3. Allowed input vs C8 must produce

### 3.1 Allowed input

- C0: l, V, I : OriginalInput.
- C1 (to define): actual places/completions, local value data.
- C2/C3 (to define): actual log/Kummer and q/theta-pilot data.
- C4/C5 (to define): actual source-witnessed output and algorithm family.
- C6 (to define): actual L_mu/V_mu, lambda_v weights, tuple denominator and
  normalization conventions. C6-STAGE1 records these as formulas/donors, not
  source instances.
- C7 (to define): actual common λO-hull with positive finite volume and qPilot
  membership. C7-STAGE1 records the actual hull as a gap.
- Existing arithmetic/local data: ArithmeticTensorTupleBlock, canonical
  hull/unit reference, FinitePlaceNormalizedUnitScalingLogVolume,
  arithmeticTupleNormalizedLogVolume and its fractional-lattice theorem.

### 3.2 C8 must produce

- Actual arithmetic vector bundle/lattice from the C7 hull.
- Actual relative determinant line bundle and structure-sheaf determinant.
- Actual weighted tensor powers/det tensor M with actual M from weights.
- Actual arithmetic degree and proof of the degree/log-volume equality in the
  C6 normalization.
- Independence of permitted M/normalization choices.
- Local finite nonarchimedean statement; global/archimedean/+inf separate.

### 3.3 Forbidden substitutions

C8 must not:
- take a free DetTensorPowerLogVolumeBookkeeping with arbitrary logVolume and
  tensorPowerExponent; that is exactly the forbidden field approach;
- use WeightedDeterminantPacket free hullLogDegree/structureSheafLogDegree/
  denominator as the actual source weights;
- define arithmetic degree as the log-volume (or conversely) to make Ob3-3 true;
- take a free determinant line bundle, arbitrary tensor power M, arbitrary
  normalization factors, or an arbitrary Frobenioid degree/realification;
- use SourceProposition37Frobenioid with effective := True / arbitrary
  degree/realification/transport as the source determinant;
- use hdeg, full-hull or the conditional ArithmeticThetaPilotBridge as a source
  hypothesis;
- identify the local single-prime statement with the global arithmetic degree or
  assume the product formula;
- use Nonempty, True, PUnit, arbitrary Type/Real/ENNReal data.

## 4. Existing Lean donors and exact limits

### 4.1 WeightedDeterminantPacket / WeightedNormalization (abstract algebra)

File WeightedNormalization.lean. Structure:
    hullLogDegree : label -> Real
    structureSheafLogDegree : Real
    denominator : label -> Nat+
Definitions:
    adjustedLogDegree i = hullLogDegree i - structureSheafLogDegree
    commonTensorDegree = prod_i denominator i
    summandTensorExponent i = prod_{j != i} denominator j
    normalizedLogVolume = sum_i adjustedLogDegree i / denominator i
    weightedLogVolume = sum_i summandTensorExponent i * adjustedLogDegree i
Proved:
    commonTensorDegree_pos, summandTensorExponent_pos,
    denominator_mul_summandTensorExponent,
    weightedLogVolume = commonTensorDegree * normalizedLogVolume.

Limits: denominator-clearing real algebra over free data. The paper's
denominators are products of actual N_v weights; no actual determinant line
bundle, tensor power, Frobenioid transport or arithmetic degree is constructed.
The free denominator field is not a source weight.

### 4.2 HullDeterminantLogVolumeReduction (log-determinant model)

File HullDeterminantLogVolumeReduction.lean. Notable declarations:
- matrixLogDet and real determinant laws for positive definite matrices;
- logDet_mul_posDef (multiplicativity), logDet_kronecker (tensor law);
- packetDet / packetLogVolume of a diagonal packet;
- profileArithmeticDegree profile = sum place, profile place;
- profileArithmeticDegree_nsmul;
- profileArithmeticDegree_adjustedDetTensorPower:
    profileArithmeticDegree (M • (arithmeticBundle - structureSheaf))
      = M * (profileArithmeticDegree arithmeticBundle -
             profileArithmeticDegree structureSheaf);
- DetTensorPowerLogVolumeBookkeeping: free logVolume : Region -> ENNReal and
  tensorPowerExponent : Nat, with the field logVolume_detTensorPower, and only a
  scalar real-line witness.

Limits: real/linear-algebra log-degree models. They do not construct the actual
arithmetic vector bundle, determinant line bundle, Frobenioid transport or
global degree. The DetTensorPowerLogVolumeBookkeeping field is satisfiable at
logVolume = 0 or top and has no nondegeneracy; it is not (Ob3-3).

### 4.3 FinitePlaceNormalizedUnitScalingLogVolume (actual local numeric donor)

File FinitePlaceNormalizedUnitScalingLogVolume.lean:
- arithmeticTupleNormalizedLogVolume
    = (1 / finrank_{Q_p} X) * (log mu(S).toReal - log mu(O).toReal);
- arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic:
    V_mu((F c) * O_hol) = -((sum_i c_i) log p),
  under ArithmeticTuplePureFractionalScalingData;
- arithmeticTupleNormalizedLogVolume_primeScalar_zpow:
    V_mu(p^k O) = -k log p;
- upper bound for sets inside a fractional-lattice container.

Limits: this proves a local normalized log-volume of a fractional lattice. It
does not construct the determinant line bundle, weighted tensor power det^⊗M,
relative determinant or arithmetic degree; it is a numeric identity in the
local Haar normalization. ArithmeticTuplePureFractionalScalingData is not
constructed anywhere.

### 4.4 C6/C7 interfaces

- C6 supplies the normalized volume convention, lambda_v weights and tuple
  denominator. C6-STAGE1 records these as to-define; no actual lambda_v/tuple
  denominator type exists.
- C7 supplies the actual λO-hull/common region and positive finite volume.
  C7-STAGE1 records the actual hull as a gap; LocalFieldProductHull is only an
  abstract finite-product donor.
- Without C6/C7 actual objects, C8 cannot construct the actual determinant
  line bundle. The C8 formulas are freezeable, but the source instance is not.

### 4.5 C10/Cor312 consumer

- Cor312ToABCBridgeInterface.regionVolume_le_normalizedWeight is the downstream
  arithmetic degree/log-volume comparison target; it is a gap, not a donor.
- StepXIContract and DetTensorPowerLogVolumeBookkeeping are downstream consumer
  shapes, not source constructions.
- The actual q-pilot/theta comparison is C9; C8 supplies the normalized degree
  input.

## 5. Consumers

- C9: uses the actual arithmetic degree/log-volume equality and C7 hull volume
  to bound possible output values and approximate Q(I); C9 must not take the
  degree equality as a free field.
- C10: assembles C8 with C1-C7/C9; C8 supplies the degree node, not a free
  determinant/logVolume parameter.
- C7 uses C8's determinant/degree readout for Ob3-3, but the route's direct C8
  consumers are C9/C10.

## 6. Statement dependencies

| Dependency | Declaration/file | Status |
|---|---|---|
| C0 allowed input | OriginalInput | exists |
| C1 actual places/completions | SourcePlaceRealization | to define; C1 gap |
| C2/C3 actual log/q data | SourceLogKummerData / SourcePilotRegionData | to define; gaps |
| C4/C5 actual output/algorithm | SourceWitnessedOutputData / SourceAlgorithmCompatibilityData | to define; gaps |
| C6 actual weights/volume | PaperNormalizedVolumeData | to define; gap |
| C7 actual λO-hull | SourceHolomorphicHullData | to define; gap |
| Abstract weighted determinant algebra | WeightedDeterminantPacket | exists abstract donor |
| Real log-determinant model | matrixLogDet / packetDet / profileArithmeticDegree | exists model |
| Local normalized volume | arithmeticTupleNormalizedLogVolume + fractional-lattice theorem | exists donor |
| Actual determinant line bundle | none | gap |
| Actual det tensor M | none | gap |
| Actual arithmetic degree | SourceProposition37Frobenioid (abstract) | not source |
| Global product formula | none | gap |

## 7. Proof dependencies (proved / abstract / gap)

Proved/abstract:
- WeightedDeterminantPacket denominator algebra and weighted/normalized volume
  identity;
- real log-determinant multiplicativity and tensor/scaling laws;
- profileArithmeticDegree additivity/nsmul/adjusted det tensor power;
- local normalized log-volume of fractional lattices and prime powers;
- DetTensorPowerLogVolumeBookkeeping free field only (not a proof).

Gap:
- actual arithmetic vector bundle/lattice from the C7 hull;
- actual relative determinant line bundle and structure-sheaf determinant;
- actual weights/N_v and det^⊗M operation with actual M;
- actual Frobenioid transport/degree/realification of the determinant;
- actual arithmetic degree/log-volume equality (Ob3-3);
- independence/divisibility of M and normalization factors;
- global all-places degree and product formula;
- archimedean and +inf branches;
- C6/C7 source instances.

## 8. Natural-language proof steps

1. From C7, take the actual common λO-hull H and its positive finite volume;
   from C6, take the actual normalized weights and lambda_v/tuple denominator.
2. Construct the actual arithmetic vector bundle/lattice determined by H and the
   actual tensor/lattice data, relative to the structure sheaf O.
3. Construct det(bundle), det(O), and the relative determinant
   det(bundle) - det(O).
4. Using actual weights, construct positive tensor powers of the direct-summand
   determinants and the inverse structure-sheaf adjustment; define det^⊗M with
   the actual positive integer M from the weights.
5. Prove real log-determinant laws for the actual determinant line bundles
   (multiplicativity, tensor/scaling) using the actual Haar/virtual-bundle
   structure, not the free abstract packet fields.
6. Prove arithmetic degree(actual det^⊗M) equals the C6-normalized log-volume of
   the original bundle with actual normalization factors; both sides constructed
   independently.
7. Prove changing M by a permitted positive multiple leaves the normalized
   readout unchanged.
8. State the local finite nonarchimedean result; assemble global degree/product
   formula and archimedean/+inf branches separately.
9. Hand the normalized degree/log-volume equality to C9/C10.

## 9. Exact gaps

G8.1 Actual arithmetic vector bundle/line bundle/determinant absent. The tree
has abstract hull sets, tensor blocks and free log-degree models, but no actual
determinant line bundle or relative determinant built from C7.

G8.2 Actual weights and M absent. WeightedDeterminantPacket.denominator is a
free Nat+ field; C6 has no actual lambda_v/tuple denominator type. The paper's
M = N_E from actual N_v weights is not constructed, so det^⊗M has no actual
exponent.

G8.3 Actual Frobenioid transport absent. SourceProposition37Frobenioid is a
reduced abstract structure (effective := True, abstract degree/realification/
transport); no actual local/global Frobenioid comparison for the determinant is
constructed.

G8.4 (Ob3-3) absent and not replaceable by a field.
DetTensorPowerLogVolumeBookkeeping.logVolume_detTensorPower is a free field,
satisfiable at 0/top, with no nondegeneracy; using it would be exactly the
forbidden path. The actual arithmetic degree/log-volume identification with
suitable normalization factors is not proved.

G8.5 C6/C7 source instances absent. C6 lambda_v/volume and C7 actual λO-hull are
to-define; C8 cannot instantiate the determinant construction without them.

G8.6 Global degree/product formula absent. The actual local block is a
single-prime finite-place ArithmeticTensorTupleBlock; no multi-prime global
carrier and no product-formula cancellation is constructed. A local equality is
not the global arithmetic degree.

G8.7 Archimedean and +inf branches absent. The finite normalized identity does
not handle archimedean factors or the extended +inf branch.

G8.8 Normalization factors and divisibility not actual. The suitable
normalization factors of (Ob3-3) and sufficient divisibility of M are not
constructed or proved invariant; only abstract denominator algebra exists.

G8.9 No relative determinant independence under base change. The paper needs
the determinant independent of choices/permutations and compatible with actual
base change; this is not proved for the abstract model.

## 10. Stage-1 acceptance and stop

statement_compiles: not applicable (no Lean declaration in this stage).
proof_body_checked: not applicable.
kernel_closed: not applicable.
target_accepted: not applicable.

This record freezes C8's actual relative determinant, weighted tensor powers,
det tensor M, arithmetic degree/log-volume equality target, donor limits,
C9/C10 consumers, and exact gaps. It explicitly rejects the arbitrary
DetTensorPowerLogVolumeBookkeeping field and does not identify Ob3-3 with a
free structure field. No Lean or production file is changed.

Stop after this stage-1 record. Next executable step is C8 stage 2: freeze the
actual local relative determinant/degree data type from C6/C7, construct
det tensor M with actual weights/M, and prove the local normalized
degree/log-volume equality; keep global product formula, archimedean and +inf
as child nodes.
