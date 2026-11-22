# N8 group 6 — stage 1: hull, arithmetic degree = normalized log-volume, (Ob3-3) / qSigned

- Task: `n8-group6`, distilled chapter 06 (`logs/coordination/n8-distilled-06-hull-degree-comparison-20261018.md`).
- Stage: **1 only** (natural-language DAG: exact objects, quantifiers, consumer, donors, gaps, one smallest stage-2 statement).
- No production edit. No proof attempted. **Nothing was compiled in this stage**: `statement_compiles` is *not* claimed
  for anything below; Lean facts are read at the cited `file:line` and reported as existing declarations, not re-validated.
- Node: `n8-g6-hull-degree-obs3-qSigned` (new; stage1 complete after this file).
- Corpus: `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt` (line numbers are that file’s lines).

## 0. What this group is about

Corollary 3.12 ends in one real inequality, `-|log(q)| <= -|log(Theta)|`, obtained by (i) forming the **holomorphic hull**
of the possible images, (ii) applying the **procession-normalized log-volume** to it, and (iii) replacing `det^{tensor M}`
by an **arithmetic degree** via (Ob3-3). The tree has the three pieces separately and no theorem that puts them into one
normalization. The most consequential defect found: every in-tree `qSigned` carrier is a **raw Haar log**, while the
paper’s `-|log(Theta)|` is a *normalized* log-volume (procession average over `j in F_l^star`; on the arithmetic side the
IUT IV Prop. 1.4(i) divisor `D = finrank_{Q_p}`). The two differ by the factor `D`.

## 1. Exact paper objects and quantifiers

### 1.1 Corollary 3.12 statement (III:10324-10353)

Suppose we are in the situation of Theorem 3.11. Write

    -|log(Theta)| in R union {+inf}

for the **procession-normalized mono-analytic log-volume** (average taken over `j in F_l^star`; cf. Rmk 3.1.1 (ii)-(iv),
Prop. 3.9 (i)(ii), Thm 3.11 (i)(a)) of the **holomorphic hull** [Rmk 3.9.5 (i)] of the **union of the possible images** of a
Theta-pilot object [Def. 3.8 (i)], relative to the relevant Kummer isomorphisms [Thm 3.11 (ii)], in the multiradial
representation of Thm 3.11 (i), **regarded as subject to** (Ind1), (Ind2), (Ind3). Write

    -|log(q)| in R

for the procession-normalized mono-analytic log-volume of the image of a **q-pilot object** [Def. 3.8 (i)], relative to
the relevant Kummer isomorphisms, in the multiradial representation of Thm 3.11 (i), **not** regarded as subject to
(Ind1)-(Ind3); `|log(q)| > 0` is “easily computed in terms of the various q-parameters of the elliptic curve `E_F` at
`v in V^bad (!= empty)`” (III:10349-10351).

Conclusion: `-|log(Theta)| in R`, and `-|log(Theta)| >= -|log(q)|`, i.e. `C_Theta >= -1` for **any** real `C_Theta` with
`-|log(Theta)| <= C_Theta * |log(q)|`.

Quantifier points that must not be lost:
1. `+inf` is a legitimate *a priori* value of the symbol (III:10326-10328); the conclusion itself asserts that it is a
   **real** number. Finiteness is part of the theorem, not an assumption.
2. The proof restricts WLOG to `-|log(Theta)| < 0` (III:10354-10358) because `-|log(Theta)| >= 0` already gives
   `-|log(Theta)| >= 0 > -|log(q)|`. The two branches are *not* interchangeable with a branch where the value is `0` (G3).
3. The normalization is an **average over `j in F_l^star`**, not a sum over processions and labels.

### 1.2 Remark 3.9.5 (i) — the hull (III:7652-7680)

`alpha U subset IQ(alpha F_vQ)` containing a relatively compact subset of **finite log-volume** `> -inf`. If `alpha U` is
relatively compact, its **holomorphic hull** is *the smallest subset of the form* `alpha H = lambda * O_{alpha F_vQ}`
**containing** `alpha U`, where `lambda in IQ(-)` has **every component nonzero** (relative to the direct-sum decomposition
into fields). If `alpha U` is *not* relatively compact, the hull is `IQ(alpha F_vQ)` (whole ambient). “One verifies
immediately that the holomorphic hull is well-defined.”

So the defining universal property is *least among the single regions `lambda * O`*, with a relative-compactness clause and
a whole-ambient fallback. It is **not** “least submonoid stable under all scalings” (contrast §2.1, G8).

### 1.3 Remark 3.9.5 (ii) — `phi` (III:7681-7723)

`P` = direct product regions; `H` = hulls of the form (i); `H subset P`; the hull operation determines `phi : P -> H`
uniquely characterized by

- (P1) `phi(H) = H` for `H in H`;
- (P2) `P subset phi(P)`;
- (P3) `P1 subset P2 => phi(P1) subset phi(P2)`;

and, “since any intersection of elements of `H` which is of **finite log-volume** necessarily determines an element of
`H`”, `phi(P) = inter_{H in H, H >= P} H`. The finite-log-volume qualifier is essential: the intersection theorem is not
available for arbitrary subfamilies.

### 1.4 Remark 3.9.5 (iii) — log-volume sandwich (III:7715-7750)

With `mu_log` of Prop. 3.9 (i):

    Phi(P) = {H in H | phi(P) >= H, (mu_log(phi(P)) >=) mu_log(H) >= mu_log(P)}
    Xi(P)  = {H in H | phi(P) >= H, mu_log(H) = mu_log(P)}

and the indeterminacy in choosing `H in Phi(P)` is **compact**, since all choices lie in the compact `phi(P)`. The sandwich
`mu_log(phi(P)) >= mu_log(H) >= mu_log(P)` is the only log-volume input used later for the hull.

### 1.5 Remark 3.9.5 (vii) — `det^{tensor M}` and (Ob3-3) (III:7875-8010)

- (Ob1) possible images are regions in tensor packets of log-shells `I_k`; the arithmetic line bundle of the q-pilot is an
  `O_k`-submodule `O_k^{mdl}` with no canonical generator, only a generator up to `O_k^x`.
- (Ob2) pass from a region in `P` to its hull `phi(P) in H`: `O_k^x`-stable, hence a localization of an **arithmetic
  vector bundle**.
- (Ob3) take the determinant: arithmetic vector bundle -> arithmetic line bundle.
- (Ob3-1-1) use **suitable positive tensor powers** of the determinants of the several **direct summands** of the tensor
  packet — “corresponding to the weights”, the products of `N_v`’s — so that the result is “consistent with the
  computation of the log-volume by means of certain weighted sums”.
- (Ob3-1-2) tensor with the **inverse** of the determinant of the **structure sheaf** `O(-)`, “an adjustment to take into
  account the ramification that occurs in the various local fields”.
- (Ob3-2) the exponents need not be relatively prime; `det^{tensor M}(-)` with `M` **the uniquely determined** positive
  integer (the `N_E` of Rmk 3.1.1 (iv)) such that the operation maps [the result of tensoring `O(-)` with] an arithmetic
  line bundle to its `M`-th tensor power.
- **(Ob3-3)** (III:7977-7987): “since (Prop. 3.9 (iii)) the **arithmetic degree** of such an arithmetic line bundle may be
  interpreted, **by working with suitable normalization factors**, as the **log-volume of the original arithmetic vector
  bundle** [to which `det^{tensor M}(-)` was applied], this intermediate step ... may be omitted in discussions in which
  one is only interested in computing log-volumes.”

Quantifier points: (Ob3-3) is an **identification of two a-priori different quantities** (“may be interpreted ... as”),
with **unspecified normalization factors**. It is not an identity of two independently defined reals, and it carries no
rank/degree formula in the statement; those live in (Ob3-1)/(Ob3-2) (weights = products of `N_v`; `M` = unique `N_E`).

### 1.6 Step (xi-d)-(xi-g) (III:10823-10903)

- (xi-d): after hull + `[suitable positive tensor power of the] determinant` + `[suitably normalized, with respect to
  j in |F_l|] log-volume`, one obtains comparable objects
  `R^{<= -|log(Theta)|} := {lambda in R | lambda <= -|log(Theta)|} subset R;  -|log(q)| in R`, where **by definition**
  `-|log(Theta)|` is the (negative) log-volume of `1,circ U`, and `-|log(q)|` is the log-volume of the region arising
  from the representation of the q-pilot at `(1,0)` on `1,circ U_Q`. Quoted here: **Prop. 3.9 (iii): “global arithmetic
  degrees of objects of global realified Frobenioids may be interpreted as log-volumes”** (III:10850-10853) — the paper
  sentence behind (Ob3-3), and the only place where the degree/log-volume identification is invoked for Cor. 3.12.
- (xi-e): the multiradial construction, **followed by hull and log-volume**, yields a *collection of possible log-volumes
  of pilot-object output data* `R^{<= -|log(Theta)|} subset R`, IPL-linked to `-|log(q)| in R`.
- (xi-f): the construction of output possibilities “constitutes, in particular, a construction [**perhaps only up to some
  sort of approximation**, as a result of various indeterminacies] of the pilot-object log-volume of the input data,
  namely `-|log(q)| in R`”. The **inclusion** `-|log(q)| in R^{<= -|log(Theta)|}`, hence `-|log(q)| <= -|log(Theta)|`,
  “then follows formally”.
- (xi-g): the two tautologically equivalent computations of the q-pilot log-volume.

Note: (xi-f) is an **inclusion/membership** derived from an *approximation* property (the paper’s word), not a pointwise
comparison of two independently constructed numbers.

## 2. Lean carriers now standing for these objects (paths relative to D:/lean/)

### 2.1 Hull

| paper object | Lean declaration | file:line | comment |
|---|---|---|---|
| `lambda * O` region | `scaledRegionImage` | HolomorphicHull/SourceImageHull.lean:277 | value form `x = lam * y` |
| least hull | `holomorphicHull` | HolomorphicHull/SourceImageHull.lean:323 | `inf` over scaling-stable **submonoids** |
| candidate class | `CandidateHull` | HolomorphicHull/SourceImageHull.lean:296 | `s in Scaling -> x in H -> s*x in H` |
| (P1),(P2),(P3) | `holomorphicHull_paper_properties` | HolomorphicHull/SourceImageHull.lean:380 | proved for that class |
| source hull of images | `sourceHolomorphicHull` | HolomorphicHull/SourceImageHull.lean:404 | `holomorphicHull (sourceScalingUnits v) possibleImageSet` |
| scalings, all components non-1 | `sourceScalingUnits` | HolomorphicHull/SourceImageHull.lean:397 | the paper’s “each component of lambda nonzero” |
| `P subset phi(P)` | `possibleThetaPilotImage_subset_sourceHolomorphicHull` | HolomorphicHull/SourceImageHull.lean:408 | |
| hull on a product of local fields | `hull`, `region`, `exists_hull_eq_region` | HolomorphicHull/LocalFieldProductHull.lean:181 | **this one really is a `lambda * O`** |
| non-relatively-compact branch | `hull_eq_univ_of_not_isCompact_closure` | HolomorphicHull/LocalFieldProductHull.lean:194 | (i)’s `IQ(alpha F_vQ)` fallback |
| hull adjunction (P1)/(P3)/intersection | `HolomorphicHullAdjunction`, `hull_idem`, `hull_mono`, `hull_eq_sInter` | HolomorphicHull/HullDeterminantLogVolumeReduction.lean:358, 388, 395, 404 | card fields, theorems from them |
| paper-level ambient hull data | `IQHullLogVolumeInterface` | HolomorphicHull/SourceHullCompactnessReduction.lean:52 | `imageSet`, `hull`, `logVolume`, `unitRegion`, `scaleShift` |
| finiteness from that data | `IQHullLogVolumeInterface.hull_logVolume_lt_top` | HolomorphicHull/SourceHullCompactnessReduction.lean:95 | conditional on the interface |
| one-point witness | `singletonRealWitness` | HolomorphicHull/SourceHullCompactnessReduction.lean:112 | consistency only |
| hull cut `S = L inter [h, inf)` | `AttainedHullCut` | Theorem311/SourceK1K2HullPresentationAdoption.lean:89 | `height`, `le_height`, `mem_of_le_height` |

### 2.2 “Arithmetic degree = normalized log-volume”: three notions, two normalizations

(a) **Local field product level — proved, and the closest donor to (Ob3-3).**
- `normalizedLogVolume mu S = log (mu S).toReal - log (mu unitRegion).toReal` (HolomorphicHull/LocalFieldProductHull.lean:247).
- `normalizedLogVolume_smul`: `= log (distribHaarChar g) + normalizedLogVolume mu S` (LocalFieldProductHull.lean:331) —
  the exact “degree (log modulus) = log-volume change” law.
- `normalizedLogVolume_region`: `normalizedLogVolume mu (region lam) = log (distribHaarChar (scalingUnits lam))`
  (LocalFieldProductHull.lean:347) — the normalized log-volume of the hull region `lambda * O` **is** the log of its modulus.
- exact modulus in split coordinates: `distribHaarChar_prime_finiteCoordinates = (p ^ card iota)^{-1}`
  (Foundations/LocalFields/PadicFiniteCoordinateHaarScaling.lean:67); measure form at :30.

(b) **Arithmetic finite-place level (single prime `p`, `D`-normalized) — proved for pure-tensor fractional lattices.**
- `arithmeticTupleNormalizedLogVolume mu S = (1 / finrank_{Q_p} X) * (log (mu S).toReal - log (mu unitReference).toReal)`
  (ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean:92) — the IUT IV Prop. 1.4(i) divisor.
- `..._primeScalar_zpow`: `mu_log (p^k bullet O_hol) = -(k) log p` (:510).
- `..._fractionalLattice_mul_holomorphic`: `mu_log (F_c * O_hol) = -((sum_i c_i) log p)` (:379), under the value-group
  data `ArithmeticTuplePureFractionalScalingData` (:133) whose `localGenerator_norm : ||localGenerator i|| = p ^ (-(c i))`
  (:135) makes the right side equal to `sum_i log ||localGenerator i||`: **degree = normalized log-volume, one prime,
  proved**.
- upper bound for a set inside such a container: `..._le_of_subset_fractionalLattice_mul` (:547).
- raw-vs-normalized pair: `arithmeticTupleCanonicalHullHaarLog = log (mu canonicalHull).toReal`
  (ABCBridge/Geometry/FinitePlaceIQHullSignedLogVolume.lean:37), `arithmeticTupleIQHullUnitRegionHaarLog` (:43), genuine
  inclusion inequality `..._le_unitRegionHaarLog` (:89).
- exact unit-relative identity: `arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal`
  (ABCBridge/Geometry/FinitePlaceIQHullInterface.lean:203): `log mu(hull) = hullUnitLogVolume + log mu(unitReference)`.
- unit-relative volume via intersection indices: `arithmeticTupleLogTensorUnitLogVolume = log(idx1) - log(idx2)`
  (ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean:92), Haar-log identity (:128).

(c) **Abstract denominator-clearing algebra of (Ob3-2)/(Ob3-3) — proved, but about free data.**
- `WeightedDeterminantPacket` with `hullLogDegree`, `structureSheafLogDegree`, `denominator : label -> Nat+`
  (HolomorphicHull/WeightedNormalization.lean:25) — (Ob3-1-2) and the denominators are **structure fields**.
- `normalizedLogVolume = sum_i adjustedLogDegree i / denominator i` (:68);
  `weightedLogVolume = sum_i summandTensorExponent i * adjustedLogDegree i` (:74).
- `weightedLogVolume = commonTensorDegree * normalizedLogVolume` (:97) — this **is** log §M’s
  `(1/N) deg(D_alpha^{tensor N/r_alpha}) = deg(D_alpha)/r_alpha`, with `N = prod denominator` (:38) and
  `N/r_i = prod_{j != i} denominator j` (:43); audit status `proved` (:121).
- `profileArithmeticDegree profile = sum place, profile place` (HullDeterminantLogVolumeReduction.lean:312), with
  `..._nsmul` (:319), `..._adjustedDetTensorPower` (:334). **No consumer** outside that file (only :312, :319, :334).
- the frozen `det^{tensor M}` card: `DetTensorPowerLogVolumeBookkeeping` (:466), field
  `logVolume_detTensorPower : forall S, logVolume (detTensorPower S) = (tensorPowerExponent : ENNReal) * logVolume S` (:477)
  — i.e. (Ob3-3) itself **as a field**, with only a scalar real-line witness (:483).

### 2.3 qSigned — three distinct meanings under one name

1. **Source / Cor. 3.12 side (free real, signed comparison).**
   `SourceXifSignedComparison I v R n qSigned : Prop := qSigned <= I.sourceSignedHullLogVolume v R n`
   (HolomorphicHull/CardHullRealSignedLogVolume.lean:198), with `sourceSignedHullLogVolume = -(I.sourceRealHullVolume v R n)`
   (:114) and `sourceRealHullVolume = (I.sourceHullVolume v R n).toReal` (Corollary312/StepXI/CertificateHullWiring.lean:247).
   Sign-conversion laws to the `ENNReal` layer: :155, :176. Reduction: with the possible-image carrier the comparison is
   *equivalent* to `sourceRealHullVolume = (image-union volume).toReal` (:231), ENNReal form :259, vertex form
   `forall j, sourceLocalLogDegree (thetaPilotPoint j) <= x` (:318).
2. **Abstract Step-XI certificate.** `StepXIContract` (`qSigned`, `thetaSigned`, `targetSigned`, `q_le_target`,
   `target_le_theta`) (Corollary312/StepXI/Contract.lean:32) and
   `Cor312Conclusion contract := contract.qSigned <= contract.thetaSigned` (:46); signed refinement
   `StepXIFiniteCertificateSigned` (Corollary312/StepXI/CertificateHullWiringSigned.lean:132). Bridge to the comparison
   datum needs the **hypothesis** `hq : Real.log q = -certificate.qSigned`
   (HolomorphicHull/CertificateComparisonBridge.lean:36, :74) — the q-parameter is not computed from the certificate.
3. **Arithmetic finite-place side (actual Haar logs).** `arithmeticTupleSignedFiniteCertificate` has
   `qSigned := arithmeticTupleCanonicalHullHaarLog ...` (ABCBridge/Geometry/FinitePlaceIQHullSignedCertificate.lean:85),
   `thetaSigned := arithmeticTupleIQHullUnitRegionHaarLog ...` (:86); the “non-vacuous” variant uses
   `arithmeticTupleSignedFloorQ = min (hull log) (-1)` (FinitePlaceIQHullSignedCertificateNonvacuous.lean:55, :98).
   Related: `qSideSignedValueCondition qPilot qSigned := qSigned = -|Real.log qPilot|`
   (ABCBridge/Geometry/FinitePlaceStepVLambda.lean:477); `signedLog q := -|Real.log q|`
   (Theorem311/HullDirectednessCovolumeSignProbe.lean:361).

## 3. Actual consumer

**Primary (the one to satisfy).** `Cor312EpsilonArithmeticComparison` (ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:224),
consumed by `cor312ToABCBridge_heightBound` (:426) and `cor312ToABCBridge_abcConjecture` (:446). Its field

    regionVolume_le_normalizedWeight :
      exists D, forall a b c, IsABCTriple a b c ->
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
          <= (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + (W.logVolume W.hull).toReal + D

(:248-251) is *exactly* the epsilon-normalized “log-volume of the region <-> arithmetic degree (arithmetic weight)”
comparison, with the theta-pilot hull log-volume as additive constant. This is where a correct (Ob3-3) normalization must
feed in. Dictionary facts already accepted: `Height.logHeight_1 (abcRationalPoint a c) = log c` and
`arithmeticWeight (abcRationalPoint a c) = log (radical (a*b*c))` (:218-221).

**Secondary (Cor. 3.12 conclusion shape).** `cor312OfSourceSignedHullComparison`
(HolomorphicHull/CardHullRealSignedLogVolume.lean:435) produces `Cor312Conclusion` from `SourceXifSignedComparison`;
arithmetic mirror `arithmeticTupleSignedFloorCor312Conclusion` (FinitePlaceIQHullSignedCertificateNonvacuous.lean:245).
**Caveat**: `Cor312Conclusion` is only `qSigned <= thetaSigned` and `qSigned` is a free field in both structures, so the
consumer is satisfiable by *choosing* `qSigned` low; it does not by itself pin the paper’s quantities.

**Hull-cut consumer.** `k1BoundaryOfAttainedHullCut` (Theorem311/SourceK1K2HullPresentationAdoption.lean:181) requires an
`AttainedHullCut` (:89) *and* `hsep : forall x y, L inter Set.Ici x = L inter Set.Ici y -> x = y` (:187). Two facts:
- `AttainedHullCut` is **refuted** for a generic frozen packet (`separatedSingletonPacket_not_nonempty_attainedHullCut`,
  Theorem311/SourceK1K2HullPresentationPacketInstance.lean:122-127), so it is genuinely extra structure;
- the only in-tree attained instance takes `possibleImage c := Set.Ici (-Q.logVolume c)` **by definition**
  (Theorem311/SourceK1K2HullPresentationFamilyCutActual.lean:208, :234, :292-307), so its attainment is definitional, not
  source-derived. `hsep` holds for upper rays but *fails* for bounded `L` (`L = Set.Iic a`: both sides empty for
  `x,y > a`) and for discrete `L` (log §H: `L = Z`, `a = 0.2`, `b = 0.8`). Any use must first fix `L` and prove `hsep` there.

## 4. Exact gaps

**G1 — normalization mismatch between the two qSigned carriers (central gap).** The arithmetic certificate’s `qSigned` is
the **raw** `log mu(hull)` (FinitePlaceIQHullSignedLogVolume.lean:37, used at FinitePlaceIQHullSignedCertificate.lean:85),
while the paper’s `-|log(Theta)|` is *normalized*: procession-averaged (III:10329-10331) and, on the arithmetic side, by the
IUT IV Prop. 1.4(i) divisor `D = finrank_{Q_p}` (FinitePlaceNormalizedUnitScalingLogVolume.lean:92). **No theorem relates
the two** (no declaration mentions both `arithmeticTupleCanonicalHullHaarLog` and
`arithmeticTupleNormalizedLogVolume`). Hence `q_negative` / `q_le_hull` of the certificate are statements about
`mu(hull) < 1` in the raw normalization and cannot be read as statements about `-|log(Theta)|`.

**G2 — the source hull volume is not a Haar log-volume at all.**
`sourceSetVolume = sup_{x in S} ENNReal.ofReal (sourceLocalLogDegree x)` (HolomorphicHull/SourceImageHullVolume.lean:188)
with `sourceLocalLogDegree = sum_{i : SourceVolumeIndex} logDegreeAt ...` (:103). No measure, no modulus, no
`distribHaarChar`: the whole arithmetic side of (Ob3-3) (degree, normalization factors, `N_v` weights) has no counterpart
in the source carrier.

**G3 — the `+inf` branch is silent and `toReal` maps it to `0`.**
`sourceRealHullVolume = (sourceHullVolume).toReal` (CertificateHullWiring.lean:247) and `ENNReal.toReal top = 0`; proved
collapse: `sourceSignedHullLogVolume_eq_zero_of_degreeFaithful` (CardHullRealSignedLogVolume.lean:346). In the paper the
`+inf` branch is the *trivial* one (`-|log(Theta)| >= 0 > -|log(q)|`, III:10354-10358); in the tree it becomes
`-|log(Theta)| = 0`, a *different value* that also makes `qSigned <= 0` true for every negative `qSigned`. Any downstream
inequality using the *value* (e.g. `theta <= C * |log q|`) gets a wrong number, and the branches are indistinguishable in
`Real`.

**G4 — no procession normalization.** `SourceVolumeIndex l = ThetaPilotCarrier l x SignedLabel l`
(SourceImageHullVolume.lean:72) with `card = (lStar l + 1) * l` (:87-90), and a theta image has
`sourceLocalLogDegree = card * log (thetaValueAt ...)` (:160-169). Nothing divides by this card, or by `l - 1`, or by
anything else, while the corpus quantity is an **average over `j in F_l^star`** (III:10329-10331). The docstring itself
says “dividing by the cardinality gives the normalized ... form” (:243-246) — that division is never performed.

**G5 — (Ob3-3) is a structure field, satisfiable at `0` and at `top`.**
`DetTensorPowerLogVolumeBookkeeping` (HullDeterminantLogVolumeReduction.lean:466): `logVolume : Region -> ENNReal`,
`tensorPowerExponent : Nat` free, and the (Ob3-3) content is the field `logVolume_detTensorPower` (:477). At
`logVolume == 0` the field is `0 = M*0`; at `logVolume == top` it is `top = M*top`. There is **no** nondegeneracy
hypothesis (`0 < logVolume S`, `!= top`). So the card does not pin (Ob3-3), and its only instance (:483) is a scalar
real-line witness.

**G6 — (Ob3-1-1) weights and uniqueness of `M` are not modeled.**
`WeightedDeterminantPacket.denominator : label -> Nat+` is a **free** field (WeightedNormalization.lean:28); the paper’s
exponents are products of `N_v`’s (III:7932-7941) and `M` is “the uniquely determined positive integer” `N_E`
(III:7964-7968). The proved identity (:97) is therefore pure real algebra over free data: it does not know that the weights
are residue degrees, nor that `N` is a *least* common multiple (it is the product of the denominators). Likewise
`profileArithmeticDegree` is unused.

**G7 — `qSigned` is never tied to the actual q-parameter on the source side.** `SourceXifSignedComparison` takes any
`qSigned : Real` (CardHullRealSignedLogVolume.lean:198); the certificate takes `hq : qSigned <= ...` and
`hqneg : qSigned < 0` (:399), so `qSigned := sourceSignedHullLogVolume` satisfies it whenever the hull is negative — the
“q-pilot” can be the hull itself. The actual `q` enters only as the **hypothesis**
`hq : Real.log q = -certificate.qSigned` (CertificateComparisonBridge.lean:36) and the free condition
`qSideSignedValueCondition` (FinitePlaceStepVLambda.lean:477). What exists: `degree_of_q` as a **field** of
`SourceImageRealization` (HolomorphicHull/SourceImageHull.lean:167) and `logDegreeAt_q` (SourceImageHullVolume.lean:128),
which *unfolds* that field at `(I.theaterAt 0 0).thetaPacket.q`.

**G8 — the paper’s hull is a single `lambda * O`; the source Lean hull is a least scaling-stable submonoid.**
`sourceHolomorphicHull = holomorphicHull sourceScalingUnits possibleImageSet` (SourceImageHull.lean:404) with
`holomorphicHull = inf over scaling-stable Submonoids` (:323). The paper’s `H` is the class of single regions
`lambda * O` (III:7663-7680) and `phi(P)` is the least of *those*; the tree takes `O` = whole ambient, so the intersection
is over a much smaller class and yields a much larger region. Consequence, proved:
`sourceHolomorphicHull_logDegree_unbounded` (SourceImageHullVolume.lean:379) and
`sourceHullVolume_eq_top_of_degreeFaithful` (:428). **Therefore that `top` is evidence that the value model is the wrong
carrier, not evidence about the paper’s `-|log(Theta)|`; it must not be cited as an obstruction of the paper’s
finiteness.** Conversely the tree proves no finiteness of the paper’s object: the conditional routes are
`SourceCompactBound` (:264), `IQHullLogVolumeInterface` (:52), and `ArithmeticThetaPilotBridge`
(HolomorphicHull/SourceArithmeticThetaPilotBridge.lean:86), the last two being interfaces whose `hull_cover` / `unit_bound`
fields are *provably impossible* under degree faithfulness (`not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful`:179).

**G9 — the global (all-places) degree is not assembled.** The finite-place block is
`ArithmeticTensorTupleBlock places tuple` for a **single prime `p`** (`FinitePlaceAtPrime K p`,
ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26). The paper’s arithmetic degree is global,
`-sum_v nu_v(a_v) log N(v) + sum_{v|inf} d_v log r_v`, zero on `f in F^x` by the product formula (log §N). Nothing in
the tree sums over several primes, and no declaration states the product-formula cancellation. Even a perfect single-prime
(Ob3-3) yields only a local factor of the global degree.

## 5. Smallest stage-2 statement (precise type)

**Why this one.** Before *any* comparison of the tree’s `qSigned` with the paper’s `-|log(Theta)|`, one must know the exact
relation between the two normalizations the tree already has (G1). That relation is a finite identity, needs no source
construction, is not the target, and turns “arithmetic degree = normalized log-volume” from a slogan into a formula. It is
strictly smaller than every alternative in §6, and every later statement in this group depends on it.

**Proposed file.** `tmp/sheaf/n8/Group6Normalization.lean` (tmp only; not imported by `Project`):

    import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedCertificate
    import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

`open MeasureTheory`; `namespace LeanFormal.IUT.NumberFieldFinitePlace`; binder block copied from
FinitePlaceIQHullSignedCertificate.lean:33-39 (`{K} [Field K] [NumberField K] {p} [Fact p.Prime]`,
`{iota} [Fintype iota] {V : iota -> Type w}`, `(places : (i) -> V i -> FinitePlaceAtPrime K p)`, `(tuple : (i) -> V i)`,
`[MeasurableSpace (...)]`, `[BorelSpace (...)]`).

**Statement (verbatim type):**

    /-- Normalization reconciliation for the signed hull carrier of Step (xi). Under the additive-Haar
    normalization `mu unitReference = 1`, the certificate’s `qSigned` (the raw Haar log
    `arithmeticTupleCanonicalHullHaarLog`) is exactly `D = finrank_{Q_p}` times the degree-normalized
    (IUT IV, Prop. 1.4(i)) log-volume of the hull; the paper’s `-|log(Theta)|` is the normalized side. -/
    theorem n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume
        {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
        {iota : Type v} [Fintype iota] {V : iota -> Type w}
        (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
        (tuple : (i : iota) -> V i)
        [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
        [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
        (mu : Measure (ArithmeticTensorTupleBlock places tuple))
        [Measure.IsAddHaarMeasure mu]
        (hunit : mu (arithmeticTupleCanonicalUnitReference places tuple) = 1) :
        arithmeticTupleCanonicalHullHaarLog places tuple mu =
          (Module.finrank (Q_p) (ArithmeticTensorTupleBlock places tuple) : Real) *
            arithmeticTupleNormalizedLogVolume places tuple mu
              (arithmeticTupleCanonicalHull places tuple)

(the `Q_p` placeholder means the `ℚ_[p]` instance in the actual text; the file must use the same notation as
FinitePlaceNormalizedUnitScalingLogVolume.lean:96.)

**Expected proof body (not attempted here).** Unfold `arithmeticTupleNormalizedLogVolume`
(FinitePlaceNormalizedUnitScalingLogVolume.lean:92) and `arithmeticTupleCanonicalHullHaarLog`
(FinitePlaceIQHullSignedLogVolume.lean:37); from `hunit` get `Real.log (mu unitReference).toReal = 0`; cancel `D != 0`
from `finrank_arithmeticTensorTupleBlock_pos` (FinitePlaceArithmeticTensorBlocks.lean:103; needs `[Finite iota]`).
Expected 6-10 lines, no `sorry`.

**Dependencies / status.** statement deps: `ArithmeticTensorTupleBlock`, `arithmeticTupleCanonicalHull`,
`arithmeticTupleCanonicalUnitReference`, `arithmeticTupleCanonicalHullHaarLog`, `arithmeticTupleNormalizedLogVolume`,
`Module.finrank` (all existing, cited above). proof deps: the two definitions + `Real.log_one` + `ENNReal.toReal_one` +
`finrank_arithmeticTensorTupleBlock_pos`. Status after this file: `statement_compiles` **not run**, `proof_body_checked`
**not run**.

**What it does and does not close.** It closes G1 (normalization ambiguity; it shows that reporting the raw Haar hull log as
`-|log(Theta)|` overstates by `D`). It does **not** close (Ob3-3) itself (G5, G6), the source identification (G2, G4, G7),
the `+inf` branch (G3), the hull mismatch (G8) or the global degree (G9). It must not be reported as (Ob3-3) being proved.

**Consumer it unblocks.** `arithmeticTupleSignedFiniteCertificate.qSigned` (FinitePlaceIQHullSignedCertificate.lean:85) and
`arithmeticTupleSignedFloorCertificate.qSigned` (FinitePlaceIQHullSignedCertificateNonvacuous.lean:98) can then be restated
in the IUT IV Prop. 1.4(i) normalization, the only normalization in which the source comparison (G1/G7) can be stated.

## 6. Alternatives considered and rejected as *the* next statement

| candidate | why rejected |
|---|---|
| `SourceXifSignedComparison` itself, or the hull=image-volume identity (CardHullRealSignedLogVolume.lean:231) | this *is* the target (xi-f)/(xi-d) content |
| log §Q epsilon-approximation bridge (`forall eps>0 exists s in V, q - eps <= s` with `forall s in V, s <= theta` imply `q <= theta`) | true but 2-3 lines of real arithmetic and **adds no interface**: the missing ingredient is the *source* construction of `V` and of the approximation, i.e. G7. Add after the carriers are pinned |
| `sourceQSideNormalizedValue` / `sourceSetVolume_possibleImage_eq_iSup_sourceQSide` (SourceQSideComparison.lean:88, :96) | already proved, but under `hdeg`, the regime where the hull volume is `top` (G8); not usable as positive evidence |
| instantiating `WeightedDeterminantPacket` from `ArithmeticTuplePureFractionalScalingData` so that `normalizedLogVolume = -(sum c_i) log p` | legitimate and *next*: ~15-25 lines, needs the 8-field `ArithmeticTuplePureFractionalScalingData` (FinitePlaceNormalizedUnitScalingLogVolume.lean:133) which is **constructed nowhere**, and presupposes the convention S1 fixes. Recorded as a child node |
| a global-degree / product-formula statement | strictly larger (G9); needs a multi-prime carrier that does not exist |
| `AttainedHullCut` route (log §F/G/H) | refuted for generic packets (§3); the maintained instance defines its possible images as rays, so it cannot witness anything about the paper’s possible images |

## 7. Verification record for this stage

- Files read (under `D:/lean/`): `AGENTS.md`, `SHEAF.md`, `GOAL.md`, `SETUP.md`, `coord/STATE.md`, `coord/queue.md`,
  `coord/FRACTAL-STAGES.md`; `logs/coordination/n8-distilled-06-hull-degree-comparison-20261018.md`; corpus III ranges
  `:7640-8010`, `:10310-10400`, `:10790-10915`; the Lean files cited above.
- Commands run: reads and greps only. **No `lake env lean`, no `lean_auto.py`, no build, no axiom probe, no comparator.**
- Status fields: `statement_compiles = not_run`; `proof_body_checked = n/a`; `kernel_closed = n/a`;
  `target_accepted = false`.
- Claims about existing declarations are source-reading claims, not current-version build evidence. The `proved` audit
  records (`weightedDeterminantNormalization`, WeightedNormalization.lean:121; `certificateComparisonFaceBridge`,
  CertificateComparisonBridge.lean:89) are cited as their own recorded status, not re-validated here.
- Production files were not modified. This file is the only artifact of the package.

## 8. Handover

- Deliverable: `tmp/sheaf/n8/group6-STAGE1.md` (this file). SHA256 recorded in the package report line.
- Node `n8-g6-hull-degree-obs3-qSigned`: stage1 complete; stage2 = §5 statement, owner pending; children:
  `n8-g6-a-weightpacket-instantiation` (stage1 open), `n8-g6-b-source-normalization` (G4, stage1 open),
  `n8-g6-c-plus-inf-branch` (G3, stage1 open).
- **One next action**: create `tmp/sheaf/n8/Group6Normalization.lean` with exactly the §5 statement, run
  `lake env lean tmp/sheaf/n8/Group6Normalization.lean` (per SETUP.md, record `statement_compiles` only), then attempt the
  6-10 line proof. Do not touch production; do not state (Ob3-3) as proved.
