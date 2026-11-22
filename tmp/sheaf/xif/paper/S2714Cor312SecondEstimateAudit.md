# S2714 — Cor312 C_Theta upper estimate: source statement and formalization checklist

Date: 2026-11-06. Status: gap audit. NOT a proof of C_Theta >= -1.

## 0. Correction of framing (user clarification)

The statement

```lean
thetaHullLogVolume <= CTheta * |Real.log q|
```

is NOT an extra assumption and NOT an allowed source hypothesis. It is the
IUT IV original upper-bound estimate on the procession-normalized log-volume of
the holomorphic hull of the Theta-pilot possible images. The Lean theorem
`Cor312ComparisonData.final_bound` currently takes it as a hypothesis only
because the IUT IV construction has not been formalized; that hypothesis is a
formalization gap, not a paper condition. An "unconditional" proof means:
prove this estimate from the paper log-volume/height objects and the original
IUT IV conditions, with no additional hypothesis.

## 1. Exact source statement

Source files:

- `papers/motizuki_corpus/text/source_audit/
  IUTIII_Theorem311_pp153-159_Corollary312_pp173-186.plain.txt`
- `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`

### 1.1 IUT III Corollary 3.12 (definition and xi-f)

IUT III Corollary 3.12, lines 561-591:

```text
Corollary 3.12. (Log-volume Estimates for Theta-Pilot Objects)
Write -|log(Theta)| for the procession-normalized mono-analytic log-volume
(average over j in F_l^*) of the holomorphic hull of the union of possible
images of a Theta-pilot object, relative to the Kummer isomorphisms, in the
multiradial representation of Theorem 3.11, subject to (Ind1), (Ind2), (Ind3).
Write -|log(q)| for the analogous log-volume of the image of a q-pilot object,
not subject to (Ind1)-(Ind3). Then -|log(Theta)| in R, and
  -|log(Theta)| >= -|log(q)|,
i.e. C_Theta >= -1 for any C_Theta in R such that
  -|log(Theta)| <= C_Theta * |log(q)|.
```

Thus Corollary 3.12 itself supplies only the xi-f LOWER bound. The upper
estimate is IUT IV.

### 1.2 IUT IV Theorem 1.10 (upper bound)

IUT IV text lines 1255-1374 (Theorem 1.10 and its proof setup), especially
lines 1363-1374:

```text
Then one may take the constant C_Theta in R of [IUTchIII], Corollary 3.12,
to be
  (l+1)/(4*|log(q)|) *
    { (1 + 12*d_mod/l) * (log(d_Ftpd) + log(f_Ftpd)) + 10*(e*_mod*l + eta_prm)
      - (1/6)*(1 - 12/l^2)*log(q) } - 1,
and hence, by applying C_Theta >= -1, conclude that
  (1/6)*log(q) <= (1 + 20*d_mod/l)*(log(d_Ftpd)+log(f_Ftpd))
                  + 20*(e*_mod*l + eta_prm)
  <= (1 + 20*d_mod/l)*(log(d_F)+log(f_F)) + 20*(e*_mod*l + eta_prm).
```

Key proof lines:

- IUT IV lines 1583-1592: in order to estimate C_Theta, compute an UPPER bound
  for the procession-normalized mono-analytic log-volume of the holomorphic
  hull of the union of the possible images of a Theta-pilot object, relative to
  the Kummer isomorphisms, subject to (Ind1), (Ind2), (Ind3), at each vQ in VQ
  and each j in {1,...,l^*}.
- lines 1836-1878: the container B_I for the union of possible images;
  (Ind1)/(Ind2) via automorphism invariance, (Ind3) via upper bounds; upper
  bound (j+1)*log(pi), then weighted average and procession normalization;
  sum over vQ in VQ to bound C_Theta*|log(q)|.
- lines 1936-1947: the resulting upper bound for C_Theta, exactly the formula
  displayed above.

### 1.3 Original conditions

From IUT IV Theorem 1.10 / its proof and IUT III Corollary 3.12 situation:

1. the situation of [IUTchIII], Theorem 3.11;
2. IUT III Corollary 3.12 situation: initial Theta-data, V_bad nonempty,
   q-parameters at v in V_bad, l >= 5;
3. good reduction assumptions used in IUT IV Theorem 1.10 (IUT IV lines
   1256-1259);
4. d_mod := [F_mod:Q], 1 <= e_mod <= d_mod,
   d*_mod := 2^12 * 3^3 * 5 * d_mod,
   e*_mod := 2^12 * 3^3 * 5 * e_mod;
5. the finite set F_tpd and the constants log(d_Ftpd), log(f_Ftpd);
6. the processions average over j in F_l^* and the normalization
   (Remark 3.1.1(ii),(iii),(iv), Proposition 3.9(i),(ii), Theorem 3.11(i)(a));
7. the holomorphic hull of Remark 3.9.5(i) and the q-pilot normalization
   |log(q)| = (1/(2l))*log(q) (IUT IV lines 1358-1363);
8. the indeterminacies (Ind1),(Ind2),(Ind3) and the container B_I;
9. the explicit PNT bound eta_prm of Proposition 1.6 (already partially actual in
   IUTIV/Estimates).

## 2. Existing actual objects that can be reused

Repository objects (all must be checked for olean/axioms before use):

1. `IUTIII/.../HullDeterminantLogVolumeReduction.lean`:
   - `Cor312ComparisonData` (thetaHullLogVolume, qPilotLogVolume,
     qPilot_mem_ray, qParameter, qParameter_pos, qParameter_log_ne_zero,
     qPilotLogVolume_eq);
   - `cor312CThetaLowerBound` / `Cor312ComparisonData.final_bound`: the
     terminal real-arithmetic implication FROM the upper estimate;
   - `cor312ComparisonData_nonempty`: numeric consistency witness only.
2. `StepXI/HolomorphicHull/Volume.lean`: `StepXIFiniteCertificate`
   (finite hull, weighted values, qSigned/thetaSigned, q_le_hull, hull_le_theta,
   q_negative).
3. `StepXI/HolomorphicHull/CertificateCThetaTransfer.lean`:
   `cTheta_lower_bound_of_finiteCertificate`, still conditional on the upper
   comparison `certificate.thetaSigned <= CTheta*|log q|`.
4. `ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean`:
   - `IQHullLogVolumeInterface` (unitRegion, scaleShift, finite hull log-volume);
   - `normalizedComparisonRegion := scaleShift '' (unitRegion union {point})`;
   - `Cor312EpsilonArithmeticComparison` with the two explicit paper-link gaps;
     `regionVolume_le_normalizedWeight` is the main log-volume estimate of
     IUT IV §2 in ABC-height shape, not literally the C_Theta upper bound.
5. `ABCBridge/Geometry/FinitePlaceIQHullSharpUpperBound.lean`:
   actual Haar-log upper bound of the canonical hull by the scaled integral
   unit region (`arithmeticTupleIQHull_hull_logVolume_le_unitRegion`), useful
   local container bound.
6. `StepXI/HolomorphicHull/SourceArithmeticThetaPilotBridge.lean`:
   `ArithmeticThetaPilotBridge`: arithmetic-unit/source-theta comparison with
   `hull_cover`, `degree_compat`, `unit_bound`; gives finiteness of the source
   hull volume under the bridge fields, not the global C_Theta estimate.
7. `StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean`: concrete
   nonpositive value model with actual Haar/source-unit data; a model, not the
   literal paper inductive carrier.

## 3. Formalization checklist for the upper estimate

1. **Literal carrier and log-volume**: construct the paper
   `IQ(S^{+-}_{j+1}; n, circ D^vdash_{vQ})` carrier and its mono-analytic
   Haar log-volume (not only the named `IQHullLogVolumeInterface`).
2. **Holomorphic hull**: for each vQ and j, the holomorphic hull of the union
   of possible images of the Theta-pilot object, under (Ind1)-(Ind3).
3. **Container B_I**: construct the arithmetic container, prove
   `B_I` is preserved by the relevant automorphisms (Ind1/Ind2), and prove the
   container log-volume is 0; derive the local upper bound `(j+1)*log(pi)`.
4. **Weighted average and procession normalization**: prove the weighted
   average upper bound and the procession-normalized upper bound
   `(l+5)/4 * log(pi) <= (l+1)/4 * 4`.
5. **Sum over vQ**: sum the local upper bounds over vQ in VQ, using the
   arithmetic-degree estimate of IUT IV Step (iii) and the constant bounds
   (E1)-(E6) (partially actual in IUTIV/Estimates).
6. **Explicit constants**: instantiate d_mod, e_mod, d*_mod, e*_mod, F_tpd,
   η_prm and prove the displayed inequalities; in particular the q-normalization
   `|log(q)| = (1/(2l))*log(q)` and `|log(q)| > 0`.
7. **C_Theta construction**: define C_Theta by the IUT IV formula and prove
   `thetaHullLogVolume <= C_Theta * |log(q)|`.
8. **xi-f and final arithmetic**: combine with `qPilot_mem_ray` /
   `-|log q| <= -|log Theta|` and invoke `cor312CThetaLowerBound` to get
   `-1 <= C_Theta`; then feed the actual `Cor312ComparisonData`.

## 4. Exact current gap

```text
GAP: no actual construction of the IUT IV Theorem 1.10 upper bound
  thetaHullLogVolume <= C_Theta * |log q|
from the paper carrier/hull/log-volume objects and the original conditions.
```

Current Lean status:

- `Cor312ComparisonData.final_bound` and `cTheta_lower_bound_of_finiteCertificate`
  are correct real-arithmetic implications but take the upper estimate as a
  hypothesis; that hypothesis is the unformalized IUT IV estimate.
- `Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight` is only
  a q-vs-weight/ABC-shape gap, not a theta-vs-q upper bound.
- `ArithmeticThetaPilotBridge` gives local finiteness/degree bounds under
  explicit bridge fields, not the global C_Theta upper bound.

## 5. Non-claims

- Do NOT claim paper 3.12 / C_Theta / IUT IV estimate closed from xi-f alone.
- Do NOT present `thetaHullLogVolume <= C_Theta*|log q|` as an allowed source
  assumption; it is the target estimate to be constructed.
- Do NOT use the numeric `cor312ComparisonData_nonempty` witness as the actual
  source comparison.
- Frozen paper concrete chain and S2707 conditional target are unaffected.

## 6. Minimal build path using current actual objects

Priority: reuse actual local container/hull objects first; only the missing
global arithmetic sum and explicit constants remain.

### Stage A — local hull upper bound (mostly actual)

Reuse:

- `ABCBridge/Geometry/FinitePlaceIQHullSharpUpperBound.lean`:
  - `arithmeticTupleCanonicalHull_subset_IQHullUnitRegion` (actual inclusion);
  - `arithmeticTupleIQHull_hull_logVolume_le_unitRegion` (actual Haar-log upper
    bound of the canonical hull by the scaled integral unit region);
  - its `IQHullLogVolumeInterface` variant.
- `ABCBridge/Geometry/FinitePlaceIQHullCertificateActual.lean`:
  - `arithmeticTupleIQHullCertificate` (actual `StepXIFiniteCertificate` with
    theta endpoint = actual finite real hull log-volume, upper bound actual;
    the q endpoint is the vacuous `q = -1`);
  - `arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_le_ofReal_theta`
    (actual `hull_logVolume <= ofReal theta`).
- `IUTIV/Estimates/ElementaryEstimates.lean`: actual (E1)-(E6) components, with
  the (E1)/(E2) sums and (E3)-(E6) arithmetic bounds available.

Minimal action: replace the vacuous q endpoint `-1` by the actual q-side
normalization. Required new bridge:

```lean
qSigned = -|Real.log q|
qSigned <= hull.hullVolume
```

and the actual `qParameter_pos`, `qParameter_log_ne_zero`. This gives a
non-vacuous local certificate at the concrete arithmetic-tuple place.

### Stage B — global hull/procession assembly

Reuse:

- `PaperSignedHull` and `IQHullLogVolumeInterface` (actual named interfaces:
  ambient hull, imageSet, unitRegion, scaleShift, logVolume, finite hull, and
  normalized procession average);
- `SourceUnitRegionHaarDataActual` (actual concrete nonpositive value model, only
  as a consistency model, not the literal paper carrier);
- `HullDeterminantLogVolumeReduction` (`Cor312ComparisonData`, ray membership,
  real arithmetic final step).

Missing: the paper `IQ(S^{+-}_{j+1}; n, circ D^vdash_{vQ})` inductive-system
carrier and the per-vQ, per-j `holomorphic hull` of possible images under
(Ind1)-(Ind3). The current `IQHullLogVolumeInterface` is a named interface, not
that literal carrier; no theorem constructs its hull/log-volume from the paper
object.

### Stage C — arithmetic/height bound and constants

Reuse:

- `ArithmeticDivisorDegree.lean` (`degLinearMap`, `deg`, `ndeg`, degree
  computations, height layer, `eDegree`);
- `IUTIV/Estimates/Section1.lean` (Prop 1.7 weighted average actual; Prop 1.6
  PNT constants actual; card/estimate lemmas);
- `IUTIV/Estimates/ElementaryEstimates.lean` ((E1)-(E6)).

Missing: the IUT IV Step (iii) arithmetic-degree estimate

```text
(1+4/l)log(d_K) + (4/l)log(s_Q)
  <= (1+12 d_mod/l)(log d_Ftpd + log f_Ftpd) + 2 log l + 52
```

and the container bound `(j+1)log(pi)`, weighted/procession average, sum over
`VQ`, and the explicit constants `d_mod/e_mod/d*_mod/e*_mod/F_tpd/eta_prm`.
These are the missing global arithmetic estimates, not extra hypotheses.

### Stage D — C_Theta and terminal step

Once Stages A-C give

```lean
thetaHullLogVolume <= CTheta * |Real.log q|
```

the rest is actual:

1. build `Cor312ComparisonData` with `thetaHullLogVolume`, actual `qParameter`,
   xi-f ray membership, and `qPilotLogVolume_eq`;
2. apply `Cor312ComparisonData.final_bound` / `cor312CThetaLowerBound` to get
   `-1 <= CTheta`;
3. optionally use `StepXIFiniteCertificate` +
   `cTheta_lower_bound_of_finiteCertificate` for the certificate face.

### Minimal order of work

1. q-normalization bridge for the actual local certificate (Stage A).
2. literal carrier/hull construction (Stage B).
3. arithmetic-degree/container estimate and constants (Stage C).
4. CTheta formula + terminal arithmetic (Stage D).

Stages A/C have actual reusable pieces; Stage B is the largest missing object;
Stage D is already actual given the upper estimate.
