# Paper sign conventions for theta log-volumes

Scope: source-text analysis only. No Lean objects or fake hull data.

## 1. What `μ_log` is normalized to

In IUT III, Proposition 3.9(i) (iut3.txt:6955-7010), the local log-volumes
`μ_log` are normalized so that

* the "local holomorphic" integral structures have log-volume **0**;
* multiplication by the local uniformizer `p_v` adds **−log(p_v) < 0**.

IUT IV (iut4.txt:688-691) states the same normalization explicitly:

    μ_log(R_i) = 0,   μ_log(p·R_i) = −log(p).

Thus `μ_log` is not the pointwise function `x ↦ log |x|`. It is a
normalized measure; a set smaller than the integral structure (p-adically, a
set of elements with norm < 1) has **negative** log-volume, while a set larger
than the integral structure has positive log-volume. The zero point is the
integral structure (or the unit log-shell), not the value 1.

## 2. Theta values < 1

In IUT III the Theta-pilot object is the arithmetic divisor determined by the
theta values

    { q_v^{j^2} }_{j=1,...,l^*}   at v ∈ V_bad

(iut3.txt:899-907). For an elliptic curve over a number field, the bad-place
q-parameters satisfy `0 < q_v < 1`; consequently every theta value
`q_v^{j^2}` is also < 1, and `log(q_v^{j^2}) < 0`.

Under the μ_log normalization above, the corresponding arithmetic divisor /
hull has a **negative** signed log-volume. This is exactly why the paper writes
the Θ-pilot log-volume as `−|log(Θ)|`, not as `+|log(Θ)|`.

## 3. The paper's explicit sign conventions

IUT III, around iut3.txt:891-922:

* q-pilot log-volume: `−|log(q)| ∈ R`, with `|log(q)| > 0`; therefore
  `−|log(q)| < 0`.
* Θ-pilot log-volume: `−|log(Θ)| ∈ R ∪ {+∞}`.
* The paper explicitly warns that the notation is confusing: `−|log(Θ)|`
  is meant to be a **positive real multiple of `−|log(q)|`** (which is a
  negative real) plus a possible error term which a priori may be `+∞`.
* The positive magnitude is defined by `|log(Θ)| := −(−|log(Θ)|)`, so in the
  finite case `|log(Θ)| > 0`.

Corollary 3.12 / Theorem B (iut3.txt:1223-1229 and 10527-10535) states:

    −|log(Θ)| ∈ R,   −|log(Θ)| ≥ −|log(q)|.

The proof explicitly observes (iut3.txt:10532-10534) that one may assume

    −|log(Θ)| < 0

whenever it is finite, because an inequality `−|log(Θ)| ≥ 0` would give
`−|log(Θ)| ≥ 0 > −|log(q)|`, contradicting the desired inequality.

So the finite signed Θ-pilot log-volume is **negative**, and the inequality
`−|log(Θ)| ≥ −|log(q)|` is an inequality between two negative numbers:
it says the Θ magnitude is **at most** the q magnitude,

    |log(Θ)| ≤ |log(q)|.

Equivalently, for the constant in the paper's normalization,

    C_Θ ≥ −1   whenever   −|log(Θ)| ≤ C_Θ · |log(q)|.

## 4. Consequence for formalization

If a Lean object `globalThetaHullLogVolume` is the actual, finite,
procession-normalized mono-analytic log-volume of the hull, then it should be
the **signed** quantity

    globalThetaHullLogVolume = −|log(Θ)|   (negative in the finite case),

not the positive magnitude. Therefore:

* positive magnitude: `|log(Θ)| = −globalThetaHullLogVolume`;
* signed Θ value: `globalThetaHullLogVolume` itself;
* signed q value: `nativeGlobalQPilotNormalizedSignedLogVolume = −|log(q)|`;
* paper direction: `nativeGlobalQPilotNormalizedSignedLogVolume ≤
  globalThetaHullLogVolume` (both negative), equivalent to
  `−globalThetaHullLogVolume ≤ |log(q)|`, i.e. `|log(Θ)| ≤ |log(q)|`.

A comparison of the form

    nativeGlobalQPilotNormalizedSignedLogVolume ≤ −globalThetaHullLogVolume

is **not** the paper direction if `globalThetaHullLogVolume` is the signed
negative quantity: it becomes `−|log(q)| ≤ |log(Θ)|`, which is a trivial
negative ≤ positive statement and does not imply `|log(Θ)| ≤ |log(q)|`.

If instead `globalThetaHullLogVolume` is defined as a sum of
`log(volume.toReal)` with per-place volumes < 1, then each term is negative
and the sum is already the signed quantity `−|log(Θ)|`; it should not be
negated again for the signed comparison. Negating it produces the positive
magnitude, suitable only for a magnitude statement `|log(Θ)| ≤ |log(q)|`.

In summary:

| paper symbol | sign in finite case | formal counterpart |
|---|---|---|
| `−|log(q)|` | negative | signed q-pilot log-volume |
| `−|log(Θ)|` | negative | signed global theta-hull log-volume |
| `|log(q)|` | positive | negation of signed q value |
| `|log(Θ)|` | positive | negation of signed theta-hull value |

The paper direction `−|log(Θ)| ≥ −|log(q)|` is the magnitude inequality
`|log(Θ)| ≤ |log(q)|`, not a negative ≤ positive triviality.
