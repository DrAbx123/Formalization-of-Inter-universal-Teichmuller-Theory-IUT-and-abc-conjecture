# Attack face 1 verdict (A899): SSIneq as a volume inequality

## What A898 established (machine-level)

`Mzk1SSIneqVolumeActual` (green, olean=True):
- `wallNumeric_iff_ssIneqForm`: with `qLhs = -A`, `kappa = -sF*A`,
  `WallNumeric qLhs kappa hullLog ↔ SSIneqForm sF A hullLog`, i.e.
  `qLhs - kappa <= hullLog ↔ (sF - 1) * A <= hullLog` (pure arithmetic, no axioms);
- `ssIneq_iff_volume`: same via the interface `LgpLawInterface` (law field) and `kappa` identity.

lana steps still requiring oleans: `idAlg_lgpLaw` (IdentifiedCopies:479),
`wall_iff_of_lgpLaw` (Checks), `wall_idAlg_iff` (IdentifiedCopies:488).

## Verdict: face 1 is an EQUIVALENT REWRITING, not an independent route

The right-hand side is the SAME hull volume `logVol(hull(vcI))` (with `A = |log q|/(2l)`,
`kappa = -sF*A`).  The transformation only moves the coefficient `(sF-1)A` to the left and
rewrites it as `qLhs - kappa`; no new object and no new bound are introduced.  Therefore:
**equivalent rewriting = infeasible as a standalone path**.

## Is there an independently provable lower bound on V?

Available green/paper lower bounds for the hull volume:

1. finite place: `componentVol leastHull tensorLogShell` is bounded BELOW by
   `-(sum_j ord(scalA_{c j})) * log p` (green `componentVol_leastHull_tensorLogShell_ge`,
   VcI.lean:286), and the paper A-exponent gives `A(p,e) = (1/e)*ceil(e/(p-2))`
   (green `logShellPaperAExponent`).  At an unramified bad place (`e = 1`) this is
   `-log p` (negative).
2. archimedean: `archConstant = log(sqrt 2 * pi) ~ 1.4913` (green `Mzk1DifferentDictionaryActual`),
   counted globally once, positive (numerical value asserted at paper level).
3. `logShellIntegerIndex >= 1` gives `log index >= 0`, but this bounds the index, not the
   hull volume (the theta scaling `-(j^2/(2l))*logQ` can make V negative).

Requirement side: `req = (sF - 1) * A = ((l+1)/24 - 1/(2l)) * |log q|`; per bad place with
`|log q_v| = log p_v` the requirement contributes about `(1/24) log p_v` (for large l),
while the available lower bound at the same place is `-A(p,e) log p_v <= -log p_v` for
e=1.  Hence the two sides differ by about `(1 + 1/24) log p_v` per bad place; the global
arch term `1.4913` cannot cover this once `p_v >= 5` (or several bad places).

So the independent lower bound available today is NEGATIVE and does not imply the
requirement; what is missing is a POSITIVE lower bound for the finite theta-packet hull
(equivalently an upper bound on the `scalA` exponents beyond the A-exponent, or positivity
of the theta-value contribution).  Concretely the gap for a single unramified bad place p
is `(1 + (sF-1)/(2l)) * log p - arch >= 0` for p >= 5, and it accumulates over bad places.

## Conclusion

- Face 1 gives no new mechanism: it is the same inequality, re-expressed with `kappa`.
- The only unconditional lower bound (shell index >= 0, arch >= 0) is too weak: the finite
  `scalA` lower bound is negative.
- The missing input (needed by face 1, chain 2 and the Szpiro direction alike) is exactly a
  POSITIVE lower bound on the finite hull/packet volume; quantifying: per unramified bad
  place p the shortfall is `(1 + (sF-1)/(2l)) log p - arch`, positive for p >= 5.

Machine support: `tmp/sheaf/xif/paper/Mzk1SSIneqVolumeActual.lean` (green).
