# C9 attack: canonical vs normalized q norm at pF

Task ID: task-174. Owner: qside. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language/Lean-source attack, no Project/target edits.
Deliverable only: this file. Consumer: `n8-c9-output-region-source-route`.

Status: the full equality between the canonical completion norm on
`qCandidate.q` and the normalized/spectral `CommonPrimeCompletion` norm at the
paper bad place is **false in general**. The exact relation is a degree power:

    canonical norm = (normalized norm)^d,
    log(canonical norm) = d * log(normalized norm),

where `d = [F_v : Q_p] = relativeCompletionDegree (k := Q) (pF S)`.
Equivalently,

    normalized norm = (canonical norm)^(1/d),
    log(normalized norm) = (1/d) * log(canonical norm).

Thus `C9Paper.QPaper.qPilotLogVolume = localSignedLog C3.q` (canonical) equals
`d * PaperP6 qLog` if `C3.q` is the paper q candidate, not `PaperP6 qLog`.
The only equality case is `d = 1` (the completion is Q_p itself). Unramified
degree `f>1` still has factor `d=f`; tame totally ramified C9 type has
`d=e=ell`, hence factor `ell`.

This corrects the wording of Q2 in `C9-PROVENANCE-BRIDGE-20261025.md`: the
missing item is not an unknown canonical/normalized equality, but the explicit
normalization factor `d` and the choice of which convention C9 Q uses.

## 1. Sources read

Lean source (read-only):

- `tmp/sheaf/n8/closure/C9-CANONICAL-NORM-ATTACK-20261025.md` target scope.
- `tmp/sheaf/n8/closure/C9-PROVENANCE-BRIDGE-20261025.md`, SHA
  `2044FE3C0B8183965CBDE84CC3732F1EAB49D698210ACE239D92F1CF049FBA5A`.
- `tmp/sheaf/n8/closure/PaperQPilotNormalizedBridge.lean`, SHA
  `1A67207560D025C74D1696CFCFF80C37D988FD988B083BED0886C75EBBFE48D6`.
- `tmp/sheaf/n8/closure/PaperP6ComparisonActual.lean`, SHA
  `7F207385ACE579442EAFEA2B0EAA4815EA6F87C009248522CD713511D2B4A440`.
- `tmp/sheaf/n8/closure/PaperP6Final.lean`, SHA
  `2F2B8884E72E25CDC9758E6D0762CAE3293C954520109448F8FA6E24838D9088`.
- `tmp/sheaf/n8/closure/C7QPilotRegionActual.lean`, SHA
  `C54FD9103BCFA34C26A7E29B9372798888BE615640AC38095587D7974572734F`.
- `tmp/sheaf/n8/closure/PaperKfHaarNormActual.lean` (localDimension = d).
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedCompletion.lean`.
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean`.
- `LeanFormal/IUT/Foundations/AlgebraicGeometry/NormalizedNormSpectralBridge.lean`.
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionNormTransport.lean`.
- `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedIntegers.lean`.
- `LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotLogVolume.lean`.

Key theorem/definition names:

```text
NumberFieldFinitePlace.normalizedCompletionNontriviallyNormedField
  -- normalized/spectral norm on CommonPrimeCompletion = NormalizedCompletion
NumberFieldFinitePlace.normalizedCompletion_norm_lt_one_iff
  -- only unit-ball comparison, not equality
GeneralNormalizedNormBySpectralUniqueness.nu
  -- nu x = - WithZero.log (Valued.v x)
GeneralNormalizedNormBySpectralUniqueness.generalNormalizedNormFormula
NormalizedNormSpectralBridge.normalizedNorm_eq_formula
NormalizedNormSpectralBridge.normalizedLogNorm_eq
NormalizedNormSpectralBridge.normalizedCanonicalPowerComparison_normalized
FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow
FinitePlaceCompletionNormTransport.logNorm_eq_absNorm_mul
ArithmeticQPilotLogVolume.localSignedLog
```

## 2. Canonical norm on the completion

For `x : Completion (pF S)` (the canonical `Valued` completion),
`FinitePlaceCompletionNormTransport.logNorm_eq_absNorm_mul` gives, for `x ≠ 0`,

```text
Real.log ‖x‖_canon = V(x) * Real.log (absNorm pF),
V(x) := Multiplicative.toAdd (WithZero.unzero (valuation x)),
absNorm pF := (Ideal.absNorm (pF S).maximalIdeal.asIdeal : Real) > 1.
```

Equivalently `‖x‖_canon = absNorm^{V(x)}`. The sign convention is the one
fixed by the `Valued` norm on the adic completion; for a uniformizer `π` the
canonical norm is `absNorm^{-1} < 1` (the source theorem
`norm_eq_absNorm_zpow` and its logarithmic form are the evidence).

## 3. Normalized norm on `CommonPrimeCompletion`

`CommonPrimeCompletion (placeAtPrime S) = NormalizedCompletion (pF S)` uses the
spectral norm over `PadicScalarField (pF S) = Q_p`. By
`GeneralNormalizedNormBySpectralUniqueness.generalNormalizedNormFormula` /
`NormalizedNormSpectralBridge.normalizedNorm_eq_formula`, for `x ≠ 0`,

```text
Real.log ‖x‖_norm = - (nu(x) * Real.log (absNorm pF)) / (d : Real),
nu(x) = - WithZero.log (Valued.v x),
d = relativeCompletionDegree (k := Q) (pF S) = [F_v : Q_p].
```

`NormalizedNormSpectralBridge.normalizedCanonicalPowerComparison_normalized`
records the equivalent power identity

```text
‖x‖_norm ^ d = (absNorm ^ nu x)⁻¹   (x ≠ 0).
```

Together with `V(x) = -nu(x)` (the `Valued` convention of the adic completion
used in the same file), this gives the exact relation

```text
Real.log ‖x‖_canon = d * Real.log ‖x‖_norm
Real.log ‖x‖_norm = (1/d) * Real.log ‖x‖_canon
‖x‖_canon = ‖x‖_norm ^ d
‖x‖_norm = ‖x‖_canon ^ (1/d)
```

for nonzero `x`. The relation is a degree power, not a scalar independent of
the element; the **log** is exactly the scalar factor `d`.

`normalizedCompletion_norm_lt_one_iff` states only

```text
‖normalizedCompletionRingEquiv x‖_canon < 1 ↔ ‖x‖_norm < 1,
```

which is invariant under a positive power and therefore gives **no** equality
of norms or logs. It explains why the P6 `qNorm_lt_one` proof transferred the
strict inequality despite the different normalizations.

## 4. Application to the paper q

Actual definitions:

```text
qAtPrime S : CommonPrimeCompletion (placeAtPrime S) := q S
qUnit S : (CommonPrimeCompletion (placeAtPrime S))ˣ := Units.mk0 (qAtPrime S) ...
q S : Completion (pF S) := (qCandidate S).q
PaperQLog(S) := Real.log ‖(qUnit S : CommonPrimeCompletion (placeAtPrime S))‖_norm
localSignedLog(qCandidate S) := Real.log ‖(qCandidate S).q‖_canon
```

Therefore, for the actual nonzero `qCandidate.q`,

```text
PaperQLog(S)
  = Real.log ‖(qCandidate S).q‖_norm
  = (1/d) * Real.log ‖(qCandidate S).q‖_canon
  = (1/d) * localSignedLog(qCandidate S),

localSignedLog(qCandidate S) = d * PaperQLog(S),

d = relativeCompletionDegree (k := Q) (pF S) = C7QPilotMassActual.d S
  (= finrank_Qp (CommonPrimeCompletion (placeAtPrime S))
     = finrank_Qp (ArithmeticTensorTupleBlock ...)).
```

The equality `d = C7QPilotMassActual.d S` is the actual
`PaperKfHaarNormActual.paperKf_localDimension_eq_d` (localDimension is
`Module.finrank Q_[p] K`) and `PaperP6AlignedTarget.d_eq_finrank_block`.

### Equality cases

- `d = 1`: `pF` has completion degree one (K_v = Q_p). Then canonical and
  normalized logs agree. This is the only case of full equality.
- Unramified `d = f > 1`: still differ by `f`. Unramified does **not** give
  equality.
- Tame totally ramified C9 type `e = ell`, `f = 1`: `d = e = ell`; the factor
  is `ell`.
- General finite extension: factor is the full completion degree `d = e f`,
  not merely the ramification index `e`.

## 5. Explicit counterexample to full equality

Take the C9 tame totally ramified local type: `K/Q_p` of degree `e = ell >= 5`,
totally ramified, residue field `F_p`, uniformizer `π`, `π^ell = p u`,
`u ∈ Z_p^×`. Then `absNorm = p`, `d = ell`.

Canonical norm:

```text
‖π‖_canon = p^{-1},        localSignedLog(π) = -log p.
```

Normalized/spectral norm:

```text
‖π‖_norm = p^{-1/ell},     PaperQLog(π) = -(log p)/ell.
```

Ratio:

```text
localSignedLog(π) / PaperQLog(π) = ell = d.
```

Thus the two numbers are not equal for `ell>1`; the strict inequality
`<1` holds for both, but the logarithms differ by the exact factor `ell`.
The same computation for an unramified degree-`f` extension with uniformizer
`p` gives canonical `p^{-f}` and normalized `p^{-1}`, again ratio `f>1`.

## 6. Consequence for C9Paper

`C9Paper.QPaper` defines

```text
QPaperScalar.value = localSignedLog C3.q
QPaper.qPilotLogVolume = (scalar.value : WithTop Real).
```

If `C3.q = qCandidate S` and `C3.place = placeAtPrime S`, then

```text
QPaper.qPilotLogVolume = d * PaperQLog(S),     not PaperQLog(S).
```

Meanwhile `C9Paper.ThetaPaper.thetaLogVolume` is defined through
`C6ActualIQData.normalizedLogVolume`, i.e. it is already degree-normalized
(the `1/D` factor is in its definition). Therefore

```text
ThetaPaper.thetaLogVolume = normalizedTheta(S) = PaperP6 normalizedTheta
                          = PaperQLog-scale, not canonical localSignedLog-scale,
QPaper.qPilotLogVolume = d * normalized Q.
```

The existing C9Paper inequality `Q.qPilotLogVolume <= Theta.thetaLogVolume`
(and `QPaperInRleq`) is a comparison between a canonical q log and a
normalized theta log. It is **not** the paper P6 `Q<=Theta` comparison unless
`d=1`. For the C9 local type with `d=ell>1`, it is off by the factor `ell` on
the Q side.

Two correct repairs are available; one must be chosen explicitly and recorded:

1. **Normalized Q (recommended for matching C6/C9 Theta):** define
   `QPaper.qPilotLogVolume_norm := localSignedLog(qCandidate)/d` and use this
   in `QPaperInRleq`/`ValuesPaper` comparisons; or
2. **Canonical Theta:** keep Q canonical and define
   `ThetaPaper.thetaLogVolume_canon := d * normalizedTheta`, converting the
   C6 normalized log volume to the canonical normalization.

Do not mix conventions. The C9 source target must state which one is used.

## 7. Relation to previous C9 provenance report

The earlier `C9-PROVENANCE-BRIDGE-20261025.md` Q2 called the required input
`CanonicalNormalizedNormEquality (pF S)`, phrased as an unknown equality. That
phrasing is now corrected:

- full equality is false for `d>1`;
- the exact relation is `localSignedLog = d * PaperQLog`;
- `C9Paper.QPaper` currently uses the canonical (left) side;
- to identify with PaperP6 C6 normalizedLogVolume, use the normalized side
  `localSignedLog/d` or convert Theta to canonical.

This is not a missing theorem about equality; it is a normalization-convention
mismatch with exact factor `d`. The only unresolved formal Lean item is a named
lemma packaging the factor (the relation itself is the algebra of the actual
`generalNormalizedNormFormula` and `logNorm_eq_absNorm_mul`; no such packaged
lemma was found in the tree).

## 8. Exact remaining Lean gap

A direct Lean theorem of the form

```lean
theorem localSignedLog_eq_completionDegree_mul_normalizedLog
    (S : SourceInitialThetaData l) :
  localSignedLog (qCandidate S) =
    (relativeCompletionDegree (k := Q) (pF S) : ℝ) *
      Real.log ‖(qUnit S : CommonPrimeCompletion (placeAtPrime S))‖
```

(and its normalized inverse) is not present as a single named declaration.
Its ingredients are present in the source files above; a stage2 Lean task can
assemble it from
`normalizedLogNorm_eq`, `logNorm_eq_absNorm_mul`, and the identification
`nu = -V`/`qAtPrime = qCandidate.q`, with the local `d` equality
`paperKf_localDimension_eq_d`. Until that lemma is written, all C9Paper
Q/Theta provenance comparisons must carry the factor `d` explicitly.

## 9. Verdict

- Full canonical/normalized equality: **false in general**.
- Exact relation: `canonical = normalized^d`;
  `log canonical = d * log normalized`;
  `log normalized = (1/d) * log canonical`.
- `d = [F_v : Q_p] = relativeCompletionDegree (pF S) = C7QPilotMassActual.d S`.
- Equality only for `d=1`; unramified degree `f>1` still differs by `f`;
  tame totally ramified C9 has factor `ell`.
- C9Paper `QPaper.qPilotLogVolume` is canonical; PaperP6 `qLog` is normalized;
  they differ by `d` and are not identifiable without the conversion.
- C9Paper `ThetaPaper.thetaLogVolume` is C6 degree-normalized; therefore the
  existing C9 Q<=Theta comparison mixes conventions unless Q is divided by `d`
  or Theta is multiplied by `d`.
- `target_accepted=false`; no target was edited; no arbitrary equality was
  assumed.

## 10. Citations

- `FinitePlaceNormalizedCompletion.lean` (normalized/spectral norm; identity
  ring equiv; homeomorphism).
- `GeneralNormalizedNormBySpectralUniqueness.lean` (`nu`, `generalNormalizedNormFormula`).
- `NormalizedNormSpectralBridge.lean` (`normalizedNorm_eq_formula`,
  `normalizedLogNorm_eq`, `normalizedCanonicalPowerComparison_normalized`).
- `FinitePlaceCompletionNormTransport.lean` (`norm_eq_absNorm_zpow`,
  `logNorm_eq_absNorm_mul`).
- `FinitePlaceNormalizedIntegers.lean` (`normalizedCompletion_norm_lt_one_iff`).
- `ArithmeticQPilotLogVolume.lean` (`localSignedLog`, `qNorm_lt_one`).
- `PaperQPilotNormalizedBridge.lean` (`qLog_eq_c6NormalizedLogVolume_qPilot`).
- `PaperP6ComparisonActual.lean`, `PaperP6Final.lean` (normalizedTheta and
  finite theta).
- `C9Paper.lean` (QPaper/ThetaPaper scalar and normalized-log fields).

End of C9-CANONICAL-NORM-ATTACK-20261025.