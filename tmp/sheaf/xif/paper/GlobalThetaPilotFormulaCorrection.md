# Global Theta-pilot formula correction: sign, index and normalization

Date: 2026-10-28. Source-check only; no Lake/Lean.

## 1. Source definitions

IUT II (source-extract/iut2.txt lines 99-108) fixes:

* `q_v` is the q-parameter at `v in V_bad`;
* the theta values at l-torsion points are (up to a 2l-th root of unity)
  `q_v^(j^2)`, for `j = 1, ..., l*`.

IUT III (iut3.txt lines 600-625, 890-925) repeats that the LGP-monoid
theta values are `{q_v^(j^2)}_{j=1,...,l*}` and that `-|log(Theta)|` is the
log-volume of the holomorphic hull of the union of possible Theta-pilot
images, subject to (Ind1), (Ind2), (Ind3).

IUT III (iut3.txt line 134) records the label decomposition

  `|Fl| = Fl/{+/-1} = {0} union Fl*`

so `Fl*` is the nonzero paired-label set; it has cardinal `l*`, not
`2l*+1`.  Corollary 3.12 (iut3.txt lines 10499-10535) takes the average over
`j in Fl*`.

## 2. Errors in the current raw candidate

The current `GlobalThetaPilotLogVolumeActual` defines

  baseQReal b = ||q_v||,
  thetaValueFromQ b j = (baseQReal b)^(j^2),
  localThetaLogVolume b = (card SignedLabel)^(-1) * sum_j -log(thetaValueFromQ b j),
  globalThetaPilotLogVolume = sum_{b in V_bad} localThetaLogVolume b.

This has three mismatches with the source:

1. Sign: for the actual contracting q_v (`0 < q_v < 1`, source q = 1/5),
   `log(q_v^(j^2)) = j^2 log q_v < 0`.  The paper's `-|log Theta|` is a
   negative log-volume (a positive multiple of the negative `-|log q|`);
   the current `globalThetaPilotLogVolume` is the positive magnitude
   `|log Theta|`, not the paper's negative `-|log Theta|`.

2. Index/cardinality: the paper averages over `j in Fl*`, cardinal `l*`.
   The current code averages over the project's `SignedLabel l.value`, i.e.
   `-l* <= j <= l*`, cardinal `2l*+1 = l`, including 0 and both signs.
   This is not the paper's `Fl*` and changes the normalization.

3. Raw theta values vs holomorphic hull: the paper's `-|log Theta|` is the
   log-volume of the holomorphic hull of the union of possible images
   (subject to Ind1/2/3).  The current sum of raw `-log q_v^(j^2)` is not
   the hull log-volume; the hull can be smaller than the raw theta-value
   sum.

## 3. Correct raw formulas

With the source labels `j = 1,...,l*`, the per-place raw theta-value
log-volume is

  L_v = (1/l*) sum_{j=1}^{l*} log(q_v^(j^2))
      = (1/l*) (sum_{j=1}^{l*} j^2) log q_v
      = ((l*+1)(2l*+1)/6) log q_v.

For `0 < q_v < 1`, this is negative, and the raw positive magnitude is

  `|log Theta_v|_raw = ((l*+1)(2l*+1)/6) |log q_v|`.

Thus the raw coefficient is

  C_source = (l*+1)(2l*+1)/6.

For `l = 5`, `l* = 2`, so C_source = 5/2 = 2.5.

The project's SignedLabel average gives the different coefficient

  C_project = l*(l*+1)/3

(for l=5: 2).  Both formulas are > 1 for every prime l >= 5.

Consequently, if one uses raw theta values and the global q-pilot
magnitude

  |log q| = sum_{v in V_bad} |log q_v|,

then the raw candidate gives

  |log Theta|_raw = C * |log q| > |log q|,

which violates the direction of Corollary 3.12

  -|log Theta| >= -|log q|  (equivalently |log Theta| <= |log q|).

Therefore the raw theta-value sum cannot be the paper's
`-|log Theta|`; the missing reduction is the actual holomorphic hull and
its (Ind1)-(Ind3) indeterminacies.

## 4. Reciprocal hypothesis is not the source convention

Replacing `q_v^(j^2)` by `q_v^(-j^2)` would flip the sign: for
`0 < q_v < 1`, `log(q_v^(-j^2)) = -j^2 log q_v > 0`.  Then the theta-value
sum would be positive while the paper's `-|log Theta|` is a negative
multiple of `-|log q|`.  The source uses `q_v^(j^2)`, not the reciprocal;
no reciprocal correction is source-faithful.

## 5. Corrected candidate and remaining object

Correct sign:

  `-|log Theta|_raw = -C * sum_{v in V_bad} |log q_v|`

with `C = (l*+1)(2l*+1)/6` for the source `Fl*` labels.  This is negative,
as required.  The corresponding raw positive magnitude is `C * sum |log q_v|`.

However, Corollary 3.12 requires the **holomorphic hull** log-volume, not
the raw theta-value sum.  The exact next object is the actual holomorphic
hull of the union of possible Theta-pilot images and the Ind1/Ind2/Ind3
quotient, whose log-volume can be smaller than the raw `C * sum |log q_v|`.
Only after constructing that hull can the inequality direction be judged.

## 6. Bottom line

* `thetaValueFromQ = q_v^(j^2)` is correct (not reciprocal).
* The paper averages over `Fl*` (cardinal `l*`), not over `SignedLabel`
  (cardinal `l`); the current card normalization is wrong.
* The current globalThetaPilotLogVolume is `|log Theta|` raw (positive), not
  the paper's negative `-|log Theta|`; the paper quantity is its negative.
* Raw coefficient over the source labels is `(l*+1)(2l*+1)/6`, which is
  `>1` for every prime `l >= 5` (l=5: 2.5); the raw theta-value sum cannot
  satisfy Cor 3.12 against the global q-pilot sum.
* The missing actual object is the holomorphic hull/Ind quotient, not a
  different sign or reciprocal convention.

No inequality is asserted in this analysis.