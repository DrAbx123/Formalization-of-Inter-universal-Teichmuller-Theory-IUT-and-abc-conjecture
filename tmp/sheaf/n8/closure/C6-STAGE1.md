# C6 — Paper normalized volume: SHEAF stage-1 record

Task ID / group / owner / date: C6 / N8 closure / primespine / 2026-10-22
Goal node / SHEAF stage: C6 PaperNormalizedVolume / stage 1 only.
Files: write tmp/sheaf/n8/closure/C6-STAGE1.md (this file). No Lean file is written or changed.
Integration/build owner: C6 owner; C10/C8 integrator later. Build not applicable to this document.
Shared interfaces/conflicts: C0 allowed input l,V,I : OriginalInput; C1 actual places/weights; C3 actual q/theta; C7 hull data. Do not edit C0/C1/C2/C3/C7 files. C6 consumers are C8 and C10.
Continuation: after stage-1 review, C6 stage 2 statement for the numerical conventions at actual places/tuples; Ob3-3, label averaging and det tensor M remain separate children.
Acceptance: stage-1 record only; no Lean compile, no proof claim.

## 1. Mathematical target (objects, quantifiers, hypotheses)

C6 fixes the paper's numerical conventions. It does not construct the hull,
the theta-pilot, the arithmetic tensor carrier or the global degree by itself.

### 1.1 Local L_mu and V_mu

Let D be the dimension/degree of the local block (in the arithmetic finite-place
case D = finrank_{Q_p} of the tensor block), let O be the reference lattice
(canonical unit reference / O_hol), and let mu be the additive Haar measure on
the ambient block. For a measurable set S of positive finite mass define

    L_mu(S) := Real.log ((mu S).toReal)
    V_mu(S) := (L_mu(S) - L_mu(O)) / D.

Then the exact general formula is

    L_mu(S) = D * V_mu(S) + L_mu(O),   D != 0,

for sets S with positive finite mass. The unit-reference corollary is

    mu(O) = 1  =>  L_mu(S) = D * V_mu(S).

These are numerical conventions, not the paper's -|log(Theta)| and not
(Ob3-3). The existing Group6Normalization file proves the hull instance of this
conversion; C6 must not reprove the same local identity.

### 1.2 Prime-scalar calibration

For the canonical hull/unit reference and the prime scalar p, the
degree-normalized local log-volume satisfies

    V_mu(p^k * O) = -(k : Real) * Real.log p,   k : Int,

i.e. mu_log(p^k O) = -k log p in the IUT IV Prop. 1.4(i) normalization. This is
the existing arithmeticTupleNormalizedLogVolume_primeScalar_zpow calibration;
C6 must reuse it, not write another synonymous lemma.

### 1.3 Local weights lambda_v

Let F_mod be the base number field, p a rational prime, v a finite place of the
upper field K lying over a place v_bar of F_mod. The paper's non-normalized
weight [K_v : (F_mod)_v_bar]^(-1) must be replaced, when working with the
degree-normalized log-volumes of IUT IV Prop. 1.4(i), by the weight

    lambda_v := [K_v : Q_p] / [K_v : (F_mod)_v_bar]
              = [(F_mod)_v_bar : Q_p].

For the finite local extension one has [K_v : Q_p] = localRamificationIndex *
localResidueDegree (the actual local e/f product) and similarly for
(F_mod)_v_bar; hence lambda_v is the absolute local degree of the lower place.
The exact field-degree identities must be proved from the actual places, not
postulated as a weight field.

### 1.4 Tuple weights and denominator

For a finite index set A of tensor factors and for each alpha in A a collection
of upper places w_alpha over a fixed lower place v_Q, the normalized weight of a
tuple w = (w_alpha) is

    prod_{alpha in A} lambda_{w_alpha}.

The tuple weight used in the paper is this product divided by the sum over all
collections of upper places (repetitions allowed) of the same product:

    weight(w) := (prod_alpha lambda_{w_alpha})
                 / (sum_{w'} prod_alpha lambda_{w'_alpha}).

The denominator is a sum over all collections {w_alpha}_{alpha in A} of upper
places over v_Q, with repetitions allowed. It must be proved nonzero (indeed
positive) from the actual finite set of upper places and positive lambda. The
Lean index of the current tuple/tensor block must be proved to correspond to
these collections; do not silently use a different index or a function type
without the repeated-label convention.

### 1.5 Procession average and label set

The paper's procession-normalized log-volume uses an average over the label set
j in F_l^star (equivalently the appropriate signed-label quotient), and the
normalized weights of III Remark 3.1.1(ii). C6 must:

- identify the exact actual label set used (not a bare ZMod, not a model
  cardinality, not a different Index type);
- prove the average/division by the actual cardinality of that label set;
- keep the distinction between a sum over labels, a sum over processions, and
  the multiplicity of the tuple index.

### 1.6 Scope

C6 fixes numerical conventions only. It does NOT automatically prove:

- (Ob3-3), i.e. the arithmetic-degree/log-volume identification;
- the determinant/tensor-M construction of (Ob3-1)/(Ob3-2);
- the global all-places degree or product formula;
- the +inf/unbounded branch of the extended log-volume;
- the source-to-arithmetic comparison (C7/C8).
It supplies the exact normalization inputs that C8/C10 consume.

## 2. Paper anchors

- coord/N8-CLOSURE-ROUTE.md section 4 C6: L_mu/V_mu and
  L = D V + L(O), mu(O)=1, primeScalar_zpow, local/tuple weights, tuple
  denominator, procession average, label sets; consumers C8/C10.
- IUT IV Prop. 1.4(i), corpus 671-682: normalized log-volume on finite
  extensions of Q_p; mu_log(R_i)=0, mu_log(p R_i)=-log p; tensor-product
  version for nonempty E subset I.
- IUT IV Remark 1.7.1, corpus 1009-1054: replacement of weights
  [K_v:(F_mod)_v]^(-1) by [(F_mod)_v:Q_vQ]; tuple normalized weights with
  repetitions; lambda_e = [(F_mod)_v:Q_vQ] in R_{>0}; beta_e a normalized
  log-volume of a compact open subset.
- IUT III Remark 3.1.1(ii)-(iv): E-weighted log-volumes and normalized weights;
  source of the tensor/repeated-label shape.
- IUT III Corollary 3.12: procession average over j in F_l^star.

## 3. Allowed input vs C6 must produce

### 3.1 Allowed input

- C0: l, V, I : OriginalInput.
- C1 (to define): actual places/completions and the finite/infinite place
  binding; C6 needs the actual finite places above p and their e/f data.
- C3 (to define): actual q/theta-pilot and its tensor/local data; not required
  for the pure normalization formulas, but required for source identification.
- Existing actual arithmetic data: FinitePlaceAtPrime, localRamificationIndex,
  localResidueDegree, completionNormDegree, arithmeticTensorTupleBlock,
  canonical hull/unit reference, Haar measure.
- Existing normalization donors: Group6Normalization local identity,
  arithmeticTupleNormalizedLogVolume and its primeScalar_zpow calibration.

### 3.2 C6 must produce

- Frozen definitions of L_mu and V_mu at the actual local block (or exact
  references to the existing raw log and normalized volume definitions).
- The general identity L = D V + L(O) and the mu(O)=1 corollary at the actual
  hull/unit reference (reusing Group6Normalization; not reproving).
- The prime-scalar calibration instance.
- Definitions/theorems for lambda_v from the actual local degrees at each
  finite place, with positivity.
- Tuple weight definition with repeated places, denominator sum, and proof the
  denominator is nonzero/positive.
- Identification of the actual tuple index with collections of upper places.
- Procession/label average definition using the actual label set and cardinality.
- Compatibility of these conventions with C7/C8 consumers.

### 3.3 Forbidden substitutions

C6 must not:
- replace L_mu or V_mu by arbitrary real functions or free fields;
- divide by an arbitrary D or assume D != 0 without the actual finrank proof;
- take mu(O)=1 as a definition when the actual Haar normalization is a
  theorem/hypothesis;
- use arithmeticTupleNormalizedLogVolume_primeScalar_zpow with a different
  scalar action than the actual p^k action;
- take lambda_v as an arbitrary positive real or a structure field without the
  actual degree identity;
- define the tuple denominator as a free field or ignore repeated places;
- identify the label set with ZMod, SignedLabel or a model cardinality without
  a proved equivalence and the actual average;
- identify C6's numerical conventions with (Ob3-3), det tensor M, or the global
  arithmetic degree;
- use hdeg, full-hull or the old conditional bridge as a normalization
  hypothesis;
- use Nonempty, True, PUnit, or arbitrary Type/Real placeholders.

## 4. Existing Lean donors and exact limits

### 4.1 Group6Normalization.lean (tmp, corrected local donor)

File tmp/sheaf/n8/Group6Normalization.lean exists (95 lines; SHA
C64B6FF45093071E163962DC5175D33FE60100E497E2417532B6222B1965F931 per STATE;
local lean exit0, no sorry). It proves:

- n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume_add_log_unitReference:
    arithmeticTupleCanonicalHullHaarLog places tuple mu =
      D * arithmeticTupleNormalizedLogVolume places tuple mu
            (arithmeticTupleCanonicalHull places tuple)
      + Real.log (mu (arithmeticTupleCanonicalUnitReference ...)).toReal;
- n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume_of_unitReference_measure_one:
    the same with mu(O)=1 and the additive log term zero.

This is the corrected L = D V + L(O) donor. C6 must cite/reuse it, not write a
synonymous local identity.

Limits: it is tmp-only, not Project; it proves only the hull/raw-Haar to
normalized local conversion. It explicitly does NOT connect to the paper's
-|log(Theta)|, Ob3-3, primeScalar_zpow, label averaging, local weights or det
tensor M.

### 4.2 FinitePlaceNormalizedUnitScalingLogVolume.lean (production donor)

- arithmeticTupleNormalizedLogVolume
    = (1 / finrank_{Q_p} X) * (log(mu S).toReal - log(mu O).toReal)
  (IUT IV Prop. 1.4(i) divisor).
- arithmeticTupleNormalizedLogVolume_canonicalUnitReference = 0.
- arithmeticTupleNormalizedLogVolume_mono.
- arithmeticTupleNormalizedLogVolume_primeScalar_zpow:
    V_mu(p^k • O) = -(k : Real) * Real.log p.
- arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic:
    V_mu((F c) * O_hol) = -((sum_i c_i) * Real.log p), under the explicit
    ArithmeticTuplePureFractionalScalingData.
- arithmeticTupleNormalizedLogVolume_le_of_subset_fractionalLattice_mul:
    upper bound for sets inside such a container.

Limits: the exact fractional-lattice theorem needs
ArithmeticTuplePureFractionalScalingData, a structure not constructed anywhere;
the prime scalar theorem is available; the file does not provide lambda_v
weights, tuple denominator, label average or global degree.

### 4.3 Arithmetic tensor/canonical hull donors

- ArithmeticTensorTupleBlock, arithmeticTupleCanonicalHull,
  arithmeticTupleCanonicalUnitReference,
  arithmeticTupleCanonicalHullHaarLog, finite measure/compactness.
- finrank_arithmeticTensorTupleBlock_pos (D != 0).
- exists_arithmeticTensorTuple_fieldProduct (algebra equivalence to a finite
  product of complete ultrametric fields).
- FinitePlaceIQHullInterface hull log volume identity.

Limits: finite-place, single-prime local data. No lambda_v weights, no tuple
denominator over repeated upper places, no procession average, no global
all-places object.

### 4.4 ArithmeticQPilotGlobalNormalization.lean (q-side degree data)

- selectedLower/UpperMagnitude, absoluteDegreeNormalizedLower/UpperSignedLog,
  absoluteDegreeNormalizedSignedLog_invariant, normalizedLowerSignedLog_neg.
- local degree formulas from ArithmeticQPilotBaseChange:
  localRamificationIndex, localResidueDegree, completionNormDegree,
  sum_completionNormDegree_eq_fieldDegree, etc.

Limits: these are q-side absolute-degree normalizations and local degree
identities; they do not define the C6 lambda_v tuple weight or the repeated-place
denominator. Some are q-specific and not the general local weight convention.

### 4.5 SourceEWeightedLogVolumeData.lean (III Rmk 3.1.1 shape donor)

- EWeightedLogVolumeData with finite V, cardinality N_v, total cardinality
  N_E = prod N_v, kappa = 1/N_E.
- normalizedWeightedLogVolume = sum_v (1/N_v) log(volume S_v).
- kappa_log_eWeightedVolume_eq_weightedSum:
  (1/N_E) mu_log_E(S) = weighted sum.
- shift_pvQ_add_log and related scaling laws.

Limits: this is an abstract E-weighted normalization skeleton with cardinality
data, not the IUT IV lambda_v = [(F_mod)_v:Q_p] weights; the tensor/repeated
label version is not formalized separately; the source constant identification
is a card/gap.

### 4.6 WeightedDeterminantPacket / DetTensorPowerLogVolumeBookkeeping

- WeightedDeterminantPacket: hullLogDegree, structureSheafLogDegree,
  denominator : label -> Nat+, normalizedLogVolume = sum adjustedLogDegree /
  denominator, weightedLogVolume = sum summandTensorExponent * adjustedLogDegree,
  weightedLogVolume = commonTensorDegree * normalizedLogVolume.
- DetTensorPowerLogVolumeBookkeeping has logVolume_detTensorPower as a field.

Limits: these are abstract denominator-clearing algebra with free data. They do
not supply the paper's lambda_v denominator or the source tuple set; the
detTensorPower logVolume scaling field is not (Ob3-3).

### 4.7 SourceQSide / source volume donors

- sourceQSideNormalizedValue n j =
    card(SourceVolumeIndex l) * Real.log (thetaValueAt n 0 j).
- sourceSetVolume_possibleImage_eq_iSup_sourceQSide (needs hdeg).
- sourceQSideNormalizedValue_neg_iff etc.

Limits: this multiplies by the cardinality of SourceVolumeIndex; it is not the
paper's average over j in F_l^star, and the exact volume statements use hdeg
(forbidden as source hypothesis). It is not the C6 procession average.

## 5. Consumers

- C8: uses L_mu/V_mu, primeScalar calibration, lambda_v, tuple weights and
  denominator to form the actual determinant/tensor-power arithmetic degree.
- C10: assembles C6 with C1/C3/C7/C8; C6 supplies the numerical convention node,
  not a free weight/volume parameter.
- C7 may use C6's normalized volume for hull finiteness, but the direct C6
  consumers fixed by the route are C8 and C10.

## 6. Statement dependencies

| Dependency | Declaration/file | Status |
|---|---|---|
| C0 allowed input | OriginalInput | exists |
| C1 actual places/completions | SourcePlaceRealization / finite place binding | to define; C1 gap |
| C3 actual q/theta | SourcePilotRegionData | to define; C3 gap |
| Local L_mu/V_mu | arithmeticTupleCanonicalHullHaarLog / arithmeticTupleNormalizedLogVolume | exists |
| L = D V + L(O) | Group6Normalization theorems | exists tmp, local identity only |
| mu(O)=1 corollary | Group6Normalization theorem | exists tmp |
| primeScalar_zpow | arithmeticTupleNormalizedLogVolume_primeScalar_zpow | exists production donor |
| Local e/f degrees | localRamificationIndex / localResidueDegree / completionNormDegree | exists donor |
| lambda_v weights | no type | to define; gap |
| tuple denominator/repeated places | no type | to define; gap |
| label average | no type | to define; gap |
| global degree | no type | C8 gap |
| Ob3-3/det tensor M | DetTensorPowerLogVolumeBookkeeping free data | not C6; gap |

## 7. Proof dependencies (proved / conditional / gap)

Proved or existing:
- arithmeticTupleNormalizedLogVolume definition and canonical unit reference zero;
- primeScalar_zpow calibration;
- fractional-lattice normalized volume (conditional on explicit scaling data);
- Group6Normalization L = D V + L(O) and unit-reference corollary (tmp);
- localRamificationIndex/localResidueDegree/completionNormDegree and their
  field-degree identities;
- q-side absolute-degree normalization and invariance;
- EWeightedLogVolumeData abstract weighted-sum identity (cardinality model).

Gap:
- actual lambda_v tuple weights from real places over p;
- tuple index with repetition and positive denominator;
- actual label set and procession average;
- source instance / identification of these conventions with C1/C3/C7 data;
- transport of primeScalar_zpow calibration to the signed certificate/global
  normalization;
- global all-places degree/product formula;
- Ob3-3, det tensor M, +inf branch.

## 8. Natural-language proof steps

1. Fix actual local block X with D = finrank_{Q_p} X; prove D != 0.
2. Define L_mu(S) and V_mu(S) as above; prove L = D V + L(O) for positive
   finite measurable S by unfolding and cancelling D.
3. Specialize to mu(O)=1; get L = D V. Reuse Group6Normalization for the hull
   instance; do not reprove.
4. State the prime-scalar calibration for the actual p^k action; reuse
   arithmeticTupleNormalizedLogVolume_primeScalar_zpow.
5. From actual finite places v | v_bar | p, compute local e/f and define
   lambda_v = [K_v:Q_p]/[K_v:(F_mod)_v_bar] = [(F_mod)_v_bar:Q_p]; prove
   positivity and the e/f identity.
6. Define the tuple index as collections of upper places allowing repetitions;
   define the tuple weight product; define the denominator as the sum over all
   collections; prove the denominator positive/nonzero.
7. Identify the actual label set (F_l^star / SignedLabel quotient) and define the
   procession average by dividing by its actual cardinality; prove compatibility
   with the q-side/theta labels.
8. Show how these conventions feed C8's determinant/tensor-power degree and C10;
   do not derive Ob3-3 or det tensor M here.
9. Record +inf/unbounded branch separately.

## 9. Exact gaps

G6.1 lambda_v has no Lean type or source construction. The local e/f donor
exists, but the actual tuple weight and its positivity/degree identity are not
defined or proved.

G6.2 Tuple index/denominator missing. No Lean type represents collections of
upper places with repetitions; no sum over all collections, no denominator
positivity/nonzero theorem, and no proof that the current tensor index equals
the paper's tuple index.

G6.3 Label average missing. No Lean construction of the average over j in
F_l^star with the actual cardinality; SourceQSideNormalizedValue multiplies by
SourceVolumeIndex cardinality, not the paper average, and its exact volume
statements need hdeg.

G6.4 Local normalization not source-identified. Group6Normalization is a
tmp local conversion; it does not identify with the paper's -|log(Theta)| or
connect to the source hull/q-pilot. The primeScalar calibration is not
transported to the signed certificate or the global normalization.

G6.5 Fractional lattice data missing. arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
requires ArithmeticTuplePureFractionalScalingData, which is constructed nowhere;
the 8-field value-group data are a gap.

G6.6 No global degree/product formula. The tree has finite-place/single-prime
normalization and q-side absolute-degree data, but no multi-prime global
carrier and no product-formula/Ob3-3 identification. WeightedDeterminantPacket
and DetTensorPowerLogVolumeBookkeeping are free abstract data, not source
constructions.

G6.7 +inf/unbounded branch not handled by the finite identity.

G6.8 C1/C3 source inputs absent. Without actual places/weights and actual
q/theta data, C6 cannot instantiate the conventions at the source; it can only
freeze the numerical formulas.

## 10. Stage-1 acceptance and stop

statement_compiles: not applicable (no Lean declaration in this stage).
proof_body_checked: not applicable.
kernel_closed: not applicable.
target_accepted: not applicable.

This record freezes C6's L_mu/V_mu formulas, mu(O)=1 corollary,
primeScalar_zpow calibration, lambda_v/tuple denominator and label average
requirements, donor limits, C8/C10 consumers, and exact gaps. It explicitly
does not identify the conventions with Ob3-3, label averaging, det tensor M or
the global degree. No Lean or production file is changed.

Stop after this stage-1 record. Next executable step is C6 stage 2: freeze the
actual LambdaWeight/tuple-denominator/label-average data types from C1/C3 data,
reuse Group6Normalization and primeScalar_zpow without duplication, and hand
them to C8.
