# Attack face 5 (A903): Gauss route verdict + Arakelov difference bundle

## 1. Gauss route verdict (from A901)

`Mzk1SSIneqFromGaussActual.lean` (green, olean=True) isolates:
- lana `Iut/ThetaLink/Gauss.lean:228 avgDeg_gaussian` gives
  `avgDeg(q^{j^2}) = Wall.sFactor n * (-Real.log ‖q‖) = sF * A`;
- `Iut/Wall/Ind3.lean:130 vcI_le_hullOf` only gives `VC(I) <= hull(VC(I))` for the
  CONTAINER, not for the Gaussian/theta-pilot region;
- the arithmetic bridge `ssIneqForm_of_gaussComparison` is proved:
  `hullLogVol >= sF*A` and `0 <= A` imply `(sF-1)*A <= hullLogVol` (SSIneq form).

VERDICT: the Gauss route is an EQUIVALENT REWRITING, not a new path.  The missing lemma is
`hullLogVol >= sF * A` (equivalently `thetaPilot/Gaussian region <= hull(VC(I))`); if it
existed, SSIneq would follow immediately, so it is equivalent-level.  No such lemma is in
lana; it is recorded as the missing comparison in `gaussRows`.

## 2. Arakelov difference bundle (definition target)

lana objects to use (root Iut/ tree):
- arithmetic line bundles with `ScalingDatum` (`Iut/Arakelov/*`) and `degNorm`
  (`Iut/Arakelov/QPilot.lean:262 logVol_lgp_integral_eq_degNorm`);
- `sectDegAt` (per-section degree) in `ScalingDatum`;
- `logQAt` (`Iut/Implication/Invariants.lean:114`) for the q-pilot degree data.

Difference-bundle definition (to formalize; MODEL notation first):

  `H_j := det(hull_j) (x) L_q^{ (-(j^2 - 1)/(2l)) }`

i.e. the hull determinant bundle twisted by the inverse q-pilot line bundle raised to the
theta exponent `-(j^2-1)/(2l)` (the exponent is fixed by the scaling law
`qroot^{j^2}` and `|log q| = logQ/(2l)`; cf. `Mzk1ThetaScaleArithmeticActual`).  The
`(sF-1)`-aggregated version uses the capsule average coefficient
`(sF-1)/(2l) = c_lana` (`Mzk1RDefinitionAuditActual` / `Mzk1SzpiroFromBoxActual`):

  `H := det(hull) (x) L_q^{ -(sF-1) }`  (model; per-capsule exponent absorbed).

The required NONZERO SECTION: a rational/global section
`x : H` with `x != 0`, and its degree bound via the product formula
`deg H >= -arch(x)` (product formula), which yields
`deg det(hull) >= (sF-1)*deg L_q - arch(x)` and hence the wall IF the arch term is
dominated by the hull denominator budget.  Precise requirement:

- `x != 0` (nonvanishing on the V-bad support; needs a construction from theta constants
  or the discriminant identity, ROUTES 14 chain 3);
- `deg(H) = deg(det hull) - (sF-1)*deg L_q >= -arch(x)` (product formula);
- `arch(x)` bounded by the hull denominator budget (IUT IV Step (v)).

## 3. Interface hook for qpilot A903

Provide (interface, to be wired to lana after oleans):
```
structure ArithBundleData where
  degNorm : Real          -- deg of the arithmetic line bundle (normalized)
  archTerm : Real         -- archimedean contribution of the chosen section
structure DifferenceBundle where
  hullBundleDeg : Real
  qBundleDeg : Real
  sFm1 : Real             -- (sF - 1)
  sectionArch : Real
  section_nonzero : Prop
  deg_identity : hullBundleDeg - sFm1 * qBundleDeg = -sectionArch
```
The wall follows from `deg_identity` + `hullBundleDeg = hullLogVol` (dictionary) +
`sectionArch <= archBudget`; qpilot's A903 should supply the section construction.

## Conclusion

Face 5: Gauss route = equivalent rewriting (missing `hullLogVol >= sF*A`).  The
difference-bundle route is the honest remaining shape: need a nonzero global section of
`H = det(hull) (x) L_q^{ -(sF-1) }` and its arch bound; the section construction is exactly
the missing input and is not faked here.
