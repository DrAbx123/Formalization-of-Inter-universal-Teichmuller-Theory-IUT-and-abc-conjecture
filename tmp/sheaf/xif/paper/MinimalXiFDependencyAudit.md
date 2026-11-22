# Minimal xi-f dependency audit

Scope: dependency analysis for the final xi-f scalar comparison only. No Lean
objects are built here, and no compatibility interface is fabricated.

## 1. What the paper's xi-f actually compares

IUT III, Corollary 3.12 / Theorem B (iut3.txt:1223-1234, 10499-10535)
contains exactly two scalars and one inequality:

* `−|log(q)| ∈ R`: the procession-normalized mono-analytic log-volume of the
  image of a q-pilot object;
* `−|log(Θ)| ∈ R ∪ {+∞}`: the procession-normalized mono-analytic log-volume
  of the **holomorphic hull of the union of possible images** of a Theta-pilot
  object, subject to (Ind1), (Ind2), (Ind3);
* the inequality `−|log(q)| ≤ −|log(Θ)|`, equivalently
  `|log(Θ)| ≤ |log(q)|`.

The final scalar comparison therefore consumes:

1. an actual q-pilot scalar (negative real);
2. an actual Theta-hull signed log scalar (negative real, or the finite
   branch; the `+∞` branch is a separate case);
3. an actual proof/Prop of the inequality between them.

Nothing else is part of the scalar statement.

## 2. What the Theta-hull scalar consumes

To define `−|log(Θ)|` one must consume:

* the actual possible-image set of the Theta-pilot object (at the relevant
  labels/processions and places, after (Ind1)/(Ind2)/(Ind3));
* the actual holomorphic hull operation on that possible-image set, including
  the actual scaling/unit-region normalization;
* the actual `μ_log`/log-volume on that hull, normalized so the unit/integral
  region has log-volume 0 and finite signed hull log-volume is negative;
* the actual theta values/`2l`-th root data and Kummer action only insofar as
  they determine the possible-image set and its indeterminacies.

The scalar does **not** consume the global FrobenioidPresentation record, the
model-Frobenioid Input record, a DivisorialMonoidOn, its pullbacks,
rational-function monoid, divisor map, Frobenioid axioms, connectedness, total
epimorphicity, or the qV global divisor object's line-bundle realization.
Those are categorical presentations of the objects on which the log-volume is
evaluated; once the actual hull region and actual `μ_log` are available, the
scalar is a function of the region, not of the presentation record.

## 3. Field-by-field consumption table

| object/field | consumed by final xi-f scalar? | minimal alternative |
|---|---|---|
| actual theta value family `q_v^{j^2}` | yes, to define possible images | actual qV family + actual `2l`-th root (or the resulting image set) |
| actual `2l`-th root / `μ_{2l}` normalization | yes, for the theta values | actual algebraic-closure or completion root data |
| Kummer action / (Ind1), (Ind2), (Ind3) | yes, only to define the union of possible images | the resulting actual image set/hull, if constructed directly |
| actual possible-image set | yes | direct actual set |
| actual holomorphic hull and scaling/unit region | yes | direct actual hull set |
| actual `μ_log` on the hull (real signed, unit-normalized) | yes | real signed hull log-volume |
| actual q-pilot scalar `−|log q|` | yes | actual q scalar (e.g. sourceQPilotSignedLog / qV bad family) |
| comparison inequality | yes | actual Prop/proof `|log Θ| ≤ |log q|` |
| LGP global realified Frobenioid presentation `C^⊩_LGP`/`C^⊩_lgp` | no, not a scalar argument | only if used to construct the hull region |
| `FrobenioidPresentation` record | no | not needed for the scalar |
| `SourceModelFrobenioid.Input` | no | not needed for the scalar |
| `DivisorialMonoidOn` / `DivisorialAddMonoid` | no | not needed for the scalar |
| pullback / FSM / connectedness / total-epimorphicity / FrobenioidAxioms | no | not needed for the scalar |
| rational-function monoid / divisor map | no | not needed for the scalar |
| `globalEffectiveDivisorMonoidActual` / qV effective divisor monoid | no, unless it constructs the hull | not needed as a categorical object |
| `QPilotGlobalObject` object/divisor class/line-bundle realization | no, unless it constructs the q scalar | actual q scalar suffices |
| global arithmetic degree of qV zero-locus primes | not automatically the paper q scalar | actual qV log-volume only |

Conditional cases: a field is consumed only if the chosen construction of the
hull/image set routes through it. The categorical presentation fields are not
arguments of the hull log-volume map itself.

## 4. Why the LGP/Frobenioid interface is not required for the scalar

The paper's `μ_log` is a measure on regions (log-shells, tensor packets,
their holomorphic hulls), not a functor on the FrobenioidPresentation record.
The Frobenioid/LGP monoid data are used to *construct* the regions and their
indeterminacies; but the final scalar evaluation only reads:

    region (set/compact open) ↦ μ_log(region) ∈ R.

Therefore filling `FrobenioidPresentation`, `Input`, `DivisorialMonoidOn`,
`LGPBaseCategory`, `LGPIsFSM`, `is_LGP`, etc. is an interface exercise, not a
requirement of the scalars in Corollary 3.12. Building those compatibility
fields does not contribute to the xi-f scalar and cannot substitute for the
actual region/hull/μ_log.

The same applies to the current q-side model:
`QPilotGlobalObjectActual.qPilotGlobalObject` is an effective-divisor model
object whose degree is a sum of `log absNorm` of underlying primes; the paper's
`−|log q|` is the log-volume of the actual q-pilot image. The object/divisor
presentation is not itself the scalar; only an actual identification would be.

## 5. Minimal actual object set needed for xi-f

The minimal real-data package is:

1. `ActualThetaImageSet`: the actual union of possible Theta-pilot images
   (after the relevant indeterminacies), or a direct actual region set.
2. `ActualHolomorphicHull`: the actual holomorphic hull of that image set,
   with the actual scaling/unit-region normalization.
3. `ActualHullLogVolume`: the actual real signed `μ_log` of the hull, with
   integral/unit region normalized to 0; no `ENNReal.ofReal` of a negative
   value and no `max 0`.
4. `ActualQPilotScalar`: the actual paper `−|log q|` (negative real), from the
   actual q family/root; not a weighted theta average and not a prime-divisor
   model degree.
5. `ActualXiFComparison`: the actual proposition/proof
   `ActualQPilotScalar ≤ ActualHullLogVolume`, or the equivalent magnitude
   inequality.

Optional construction data (needed only to build items 1-2 from source): the
actual theta values/`2l`-th root, the Kummer/Ind indeterminacy action, and the
actual multiradial representation. The global FrobenioidPresentation/Input/
DivisorialMonoidOn is not in the minimal set.

## 6. Current files: keep vs not needed for the scalar

Relevant to the hull scalar:

* `GlobalThetaPilotHullLogVolumeActual.lean`: current source, but uses the old
  `sourceSetVolume` zero truncation; not final.
* `SignedHullSupActual.lean`: real signed `sSup` over `sourceHolomorphicHull`,
  closer to the scalar, but its full-hull `sSup` includes the identity point and
  is not automatically the paper hull log-volume.
* `GlobalHullSignedComparisonActual.lean`: reduces signed comparison to a
  magnitude bound, but inherits the old hull scalar; not final.
* `GlobalPositiveHullPaperXiFActual.lean`: the correct scalar reduction
  `T ≤ Q`; still needs an actual positive hull from the paper hull, not a raw
  theta sum.

Not needed for the scalar (interface/architecture):

* `GlobalRealifiedFrobenioidActual.lean`;
* `GlobalFrobenioidPresentationActual.lean`;
* `LGPFrobenioidPresentationActual.lean`;
* `LGPPhiInputActual.lean`;
* `LGPPhiInputFilledActual.lean`;
* `LGPPhiInputActualData.lean`;
* `QPilotGlobalObjectActual.lean` (only if used to identify the actual q scalar);
* `GlobalQPilotObjectActual.lean` (its `globalQPilotSignedLog` scalar is the
  potentially useful part; the collection record is not required).

These may be retained as source-level architecture, but they are not
dependencies of the final xi-f scalar and should not be built for compatibility
reasons alone.

## 7. Per-b fractional tensor scalar: LGP/Frobenioid consumption

The local per-b fractional tensor scalar is the normalized hull log-volume of
one actual bad-place Theta-pilot hull. Its only inputs are:

* the actual per-b hull (or its actual Haar volume);
* the actual unit-region Haar normalization;
* the ratio `hullVolume / unitVolume` and its real logarithm.

No LGP/Frobenioid chain is consumed by this scalar: no `FrobenioidPresentation`,
no `SourceModelFrobenioid.Input`, no `DivisorialMonoidOn`, no LGP base/FSM
record, no LGP Phi/Input, and no qV global divisor object appears in the
formula. The LGP/Frobenioid data may construct the hull region upstream, but the
per-b scalar is a function only of the actual hull volume and the actual unit
normalization. Therefore the LGP compatibility work is not required for the
xi-f scalar and should not be continued for that purpose.

The minimal local object is implemented in
`LocalPerBHullNormalizedLogActual.lean`: actual per-b hull volume, exact
unit-region normalization data, the positive ratio, and the normalized real
log. The unit normalization remains exact input data (the paper mono-analytic
normalization is a source identification), not a fabricated scalar.
