# ROUTE3-CDIVISOR — Route 3 C-Divisor actual construction

Task: task-84, R29d-stepxi. Status: construction + asset audit; no new assumptions.
Snapshot: 2026-11-13T04:08:42+08:00 Asia/Shanghai (task time); watchdog result section updated after build.
Source: HANDOFF 2026-11-13 updated version, sections 6.3-6.4, 8.2 P5, 9.4, 10.5.
Deliverable: this file plus tmp/sheaf/xif/paper/Mzk1Route3DivisorActual.lean.

## 0. Verdict

C1 (f_P) is PARTIAL: the actual function-field element f_P and its nonzero proof are
constructed, and the affine zero-ideal relation XYIdeal_neg_mul is checked in the
same file (Mathlib, not a new assumption). The full principal-divisor equality at the point at
infinity is NOT available because Mathlib has no curve divisor/order-of-vanishing
API at O.

C2 is PARTIAL: a finite product F_C of actual f_P factors over any supplied finite
family of actual curve points is constructed and proved nonzero. A canonical
representative set for C subset E[l] and the divisor equality are not constructed.

C3 and C4 are BLOCKED: no quotient isogeny E -> E/C, no pullback divisor or degree
formula exists in Mathlib/the tree.
C5 is BLOCKED for the full F_l: no finite enumeration of E[l] and no
multiplication-by-l isogeny/pullback divisor; only finite subfamily products are
constructed.

The work therefore reduces the algebraic constructor side but does not prove any of
the four target divisor equalities (C1), (C3), (C4), (C5). No toy carrier or fake
divisor equality is used.

## 1. Asset audit: what is actually available

### 1.1 Mathlib affine curve/function field: YES

File: .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean.
- FunctionField abbreviation at line 95: FractionRing CoordinateRing.
- Point inductive type at line 467 (zero or some x y h).
- CoordinateRing.XClass at line 203: class of X - C x in R[W].
- CoordinateRing.XYIdeal at line 241; XYIdeal_neg_mul at line 292:
  XYIdeal W x (C (negY x y)) * XYIdeal W x (C y) = XIdeal W x for nonsingular P.
- The file also has ClassGroup/fractional-ideal machinery, but no point-to-divisor
  function with order at the point at infinity.

Use in our file: fP is algebraMap of XClass into FunctionField; Mathlib XYIdeal_neg_mul
is exactly Mathlib XYIdeal_neg_mul. This is actual, not a model.

### 1.2 Division polynomial evaluation: YES, with a boundary

File: LeanFormal/IUT/ABCBridge/Galois/EllipticDivisionPolynomialEvaluation.lean.
- Header lines 23-40: evalDivisionPolynomial, ψ, Ψ, preΨ; the only genuine nsmul
  relation Mathlib supports is n=2; the group-law equivalence
  n • P = 0 <-> ψ_n(P) = 0 is explicitly not in Mathlib for general n.
- Useful proved APIs: evalDivisionPolynomial_eq_eval_preΨ_of_odd (odd n),
  two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero.
Boundary: this file does not enumerate E[l] or prove roots of preΨ are exactly
the x-coordinates of l-torsion points; therefore it cannot prove C5's product
identity by itself.

### 1.3 Torsion algebraicity/division fields: PARTIAL

File: LeanFormal/IUT/ABCBridge/Galois/EllipticTorsionAlgebraicity.lean.
- Header lines 25-60: prime-torsion finiteness is not unconditional; torsion
  coordinates are algebraic under the DivisionPolynomialDetectsTorsion bridge.
- Proved conditional results: divisionPolynomialDetectsTorsion_three;
  isIntegral_coordinates_of_nsmul_eq_zero_of_odd;
  pointField_finiteDimensional_of_torsion; divisionField_finiteDimensional_of_torsion.
Boundary: no actual finite Finset enumerating E[l] is constructed.

### 1.4 Source theta divisor object: NOT a curve divisor

File: LeanFormal/IUT/Foundations/AlgebraicGeometry/SourceQlThetaObjectActual.lean.
- SourceThetaDivisor S is exactly (NumberField.InfinitePlace F -> Int);
  see sourceThetaObjectDivisorType_eq and lines 191-216.
- Its degree is the weighted infinite-place degree, not a sum over curve points.
  It cannot represent div(f_P), F_C, or F_l; using it would be a type error
  disguised as a divisor.

### 1.5 Source line bundle: explicitly missing

File: LeanFormal/IUT/Foundations/AlgebraicGeometry/SourceQlThetaLineBundleFromCurve.lean.
- Lines 24-31: Definition 3.1 gives the curve but no field carrying a line bundle,
  no theta object A_Theta, no chosen geometric theta divisor, no unit comparison,
  no mu2l/l-Z/deck action or conjugate synchronization.
- Lines 155-184: inductive SourceThetaLineBundleMissingDatum and six-item list.
This confirms that the line-bundle/divisor bridge cannot be assumed here.

### 1.6 Analytic odd theta normalization: SPECIAL VALUES ONLY

Files: LeanFormal/IUT/Foundations/Theta/OddThetaNormalization.lean,
OddThetaShift.lean, OddThetaShiftSum.lean.
- OddThetaShift.lean: oddTheta_shift is the actual EtTh Proposition 1.4(ii) shift law.
- OddThetaNormalization.lean: oddThetaFraction_eval / unconditional normalized
  evaluation at i*r^j, and oddThetaSign_mul_i_zpow_neg_two_mul.
Boundary: these are analytic normalization/function equations for a theta series.
  They do not construct a line bundle section, a curve zero divisor, or the
  map from theta values to curve points. They are useful for the theta side
  (route 3 C-Theta), not for replacing C1-C5.

### 1.7 Product formula: NUMBER-FIELD units, not curve functions

File: LeanFormal/IUT/IUTII/Frobenioid/Example36ProductFormula.lean.
- productFormula_log / productFormula_finsupp: the global product formula for a
  number-field unit f : F^x, in the finite + archimedean normalization.
Boundary: a number-field unit is not a rational function on the elliptic curve;
  this cannot prove div(f_P) or div(F_C).

### 1.8 Root extension / theta line bundle / tensor image assets

- X/PaperRootExtensionEquivActual.lean: root extension equivalence and root norm;
  no curve divisor.
- X/PaperRootExtensionHaarFactorActual.lean: root Haar scaling; no curve divisor.
- X/ThetaFunctionLineBundleActual.lean: actual zero locus of q^(j^2) values,
  explicitly no line bundle/theta object; analytic values only.
- X/ThetaTensorScaledImageActual.lean: tensor scaled regions/hull; it records
  missing qVFamily-to-tensor alignment, not a curve divisor.
Boundary: these are theta/tensor-side objects, not substitutes for C1-C5.

## 2. C1-C5 status against the target statements

### C1: f_P and div(f_P) = [P] + [-P] - 2[O]

Constructed (actual):
- fP : W.Point -> W.FunctionField at Mzk1Route3DivisorActual.lean:44;
  for a nonsingular affine point P=(x,y), fP = algebraMap (XClass W x).
- fP_ne_zero at line 59: every actual f_P is nonzero.
- The affine zero-ideal relation is Mathlib's XYIdeal_neg_mul at
  .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:292:
    XYIdeal W x (C (negY x y)) * XYIdeal W x (C y) = XIdeal W x.
  It is #check-ed at the end of Mzk1Route3DivisorActual.lean and is not a new
  assumption. A wrapper theorem was deliberately not added because restating
  the large XYIdeal/FractionRing type caused a watchdog heartbeat timeout.

Gap: the target equality is a divisor equality on the complete curve. Mathlib has
no divisor/order-of-vanishing API at the point at infinity O, so the pole term
-2[O] and the full equality are not stated/proved. This is a real infrastructure
gap, not a missing algebraic manipulation.

### C2: F_C = product over (C\{O})/+-1 of (x - x(P))

Constructed (actual):
- productF at line 76: for any finite index type iota, P : iota -> W.Point,
  productF W P = ∏ i, fP W (P i).
- productF_ne_zero at line 79.

Gap: no canonical finite representative family for a cyclic subgroup C of E[l]
is constructed. The caller must supply the actual finite family; the product
definition itself is not a construction of C.

### C3: div(F_C) = sum_{P in C\{O}} [P] - (l-1)[O]

NOT PROVED. The same missing divisor theory blocks it; additionally the sum over
C\{O} requires the actual finite C data, which is not constructed.

### C4: div(F_C) = phi_C^*[O'] - l[O] (separable quotient)

NOT PROVED / BLOCKED. There is no quotient isogeny E -> E/C, no pullback of a
divisor, and no degree formula for pullback in Mathlib or in the inspected tree.
Assuming such a phi_C would be exactly the forbidden fake hypothesis.

### C5: F_l product over all nonzero l-torsion, div = [l]^*[O] - l^2[O]

NOT PROVED / BLOCKED for the full object.
- productFTorsion at line 94 is only the product over a supplied finite family of
  actual points; it is not all of E[l].
- No finite Finset enumeration of E[l] from the actual input is available.
- No multiplication-by-l isogeny or its pullback divisor is available.
- The division polynomial route is insufficient: Mathlib has prePsi but not the
  root/torsion identification and not the divisor of prePsi.

## 2.1 C2-C5 BLOCKED summary

| item | status | exact blocker | next step |
|---|---|---|---|
| C2 productF | PARTIAL | finite product exists; no canonical finite C subset E[l] / representative choice | construct finite C enumeration from actual input or state its exact data gap |
| C3 div(F_C) | BLOCKED | no principal-divisor/order API at O and no finite C divisor | curve-divisor interface + finite C data |
| C4 quotient pullback | BLOCKED | no quotient isogeny E->E/C, no pullback divisor | develop/import quotient isogeny and pullback |
| C5 full F_l | BLOCKED | no finite E[l] enumeration; no [l]-isogeny/pullback; no prePsi root identification | finite E[l] + multiplication isogeny/pullback + root theorem |

## 3. Why the listed assets do not close C3-C5

- EllipticDivisionPolynomialEvaluation proves only evaluation identities and n=2
  torsion; its own header says the general nsmul/psi equivalence is absent.
- EllipticTorsionAlgebraicity gives conditional algebraicity/division-field
  finiteness, not a finite E[l] Finset and not a quotient isogeny.
- SourceQlThetaDivisorDegreeActual's divisor carrier is infinite places of F,
  not points of E; it cannot encode [P], [-P], [O].
- SourceQlThetaLineBundleFromCurve explicitly records six missing line-bundle
  data; it does not construct phi_C or [l]^*.
- OddTheta* give analytic theta normalization, not a curve divisor theory.
- Example36ProductFormula is the number-field product formula, not a function
  divisor on E.
- PaperRootExtension*/ThetaFunctionLineBundle/ThetaTensorScaledImage are
  theta/tensor assets, not curve-divisor assets.

## 4. Minimal next steps

1. Add a real curve-divisor interface: a finitely supported integer function on
   W.Point (including O) and an order-of-vanishing/principal-divisor theorem.
   Without it, C1/C3/C5 cannot even be stated at target fidelity.
2. Prove the affine local part already available (Mathlib XYIdeal_neg_mul) and then
   prove the O-pole term separately; do not identify XIdeal with the full divisor.
3. Construct a finite representative family for a cyclic C subset E[l] from the
   actual arithmetic input; or state the exact finite enumeration gap.
4. For C4/C5, either import/develop quotient/multiplication isogenies with
   pullback divisors, or keep them as explicit blocked items; do not axiomatize.
5. For C5's division-polynomial route, prove roots(prePsi l) = x(E[l]\{O})
   up to normalization; this is currently absent from Mathlib.

## 5. Build evidence (watchdog)

File: tmp/sheaf/xif/paper/Mzk1Route3DivisorActual.lean.
Per lead's unified rule, this file is handed to the watchdog; no manual lake/lean
command is run by this worker.  Watchdog START is recorded; final START/DONE or
FAIL lines and the per-file log are to be read from:
- D:/lean/dag/watchdog/watchdog.log
- D:/lean/dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1Route3DivisorActual.lean.log

Status at final watchdog check:
- START 2026-11-12T20:23:51.256Z tmp/sheaf/xif/paper/Mzk1Route3DivisorActual.lean
- DONE EXIT=0 2026-11-12T20:24:20.676Z (29s)
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1Route3DivisorActual.olean
  (size 107720 B, mtime 2026-11-12T20:24:20Z)
- Axioms printed by the file:
  fP_ne_zero, productF_ne_zero, productFTorsion_ne_zero all depend only on
  [propext, Classical.choice, Quot.sound].
- The final #check confirms Mathlib XYIdeal_neg_mul's statement; no wrapper
  theorem is claimed because the explicit wrapper hit a heartbeat timeout and
  was removed from the minimal green core.

## 6. Exact source locations

Paper target definitions:
- HANDOFF 6.3 lines 862-881 (C1);
- HANDOFF 6.4 lines 883-946 (C2/C3/C4/C5);
- HANDOFF 8.2 P5 lines 1413-1420;
- HANDOFF 9.4 lines 1567-1585.
Our file line numbers are in section 2 above.

Mathlib gaps:
- Affine/Point.lean has Point/FunctionField/XYIdeal but no divisor API;
- DivisionPolynomial has no general torsion-root theorem;
- no isogeny/quotient/pullback-divisor API was found in the elliptic-curve tree.


## 7. task-96: minimal curve-divisor API audit (result: GAP)

Task-96 asked for the minimal algebraic-geometry API needed to turn C1/C3 into
real divisor statements. Content search result: Mathlib has the affine
coordinate ring/function field and ideal factorization, but not the order at a
point or the point at infinity.

### 7.1 What exists

- WeierstrassCurve.Affine.Point (Affine/Point.lean:467), FunctionField (:95),
  CoordinateRing.XClass (:203), XYIdeal (:241), XYIdeal_neg_mul (:292).
  These give the affine zero-ideal relation only.
- IsDedekindDomain.HeightOneSpectrum and its valuation exist in
  Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean:495 and
  .../AdicValuation.lean:328, but require an IsDedekindDomain R instance.
- ClassGroup.toPrincipalIdeal (ClassGroup/Basic.lean:48) maps function-field
  units to fractional ideals, but carries no order/coefficient at a specific
  point and no point at infinity.

### 7.2 What is missing (exact)

1. No IsDedekindDomain instance for W.CoordinateRing was found in Mathlib.
   Without it, HeightOneSpectrum/adicValuation cannot be used to define an
   affine order at XYIdeal.
2. No orderAt/OrderAt/principal-divisor API for an affine elliptic curve was
   found; Point.lean has points, ideals and the class group, not a valuation at
   a point.
3. No point-at-infinity local ring, uniformizer, or orderAtO for W.FunctionField
   was found. Projective/Point.lean gives projective points, not a projective
   function field/local parameter.
4. No WeilDivisor or PrincipalDivisor type was found in Mathlib (content search
   over Mathlib AlgebraicGeometry/RingTheory).
5. Consequently div(fP) = [P]+[-P]-2[O] is not statable in current Mathlib
   without inventing an order function; inventing one would be an unproved
   assumption. The honest status remains C1 PARTIAL.

### 7.3 Minimal supplement (implementation order)

A. Dedekind/local order at an affine point:
   - prove [IsDedekindDomain W.CoordinateRing] for W.IsElliptic (or a local DVR
     at XYIdeal), then construct HeightOneSpectrum.ofPrime from XYIdeal maximality;
   - define orderAtAffine (P) : W.FunctionField^x -> Int using the normalized
     HeightOneSpectrum.valuation;
   - prove orderAtAffine_mul, orderAtAffine_zero, and
     orderAtAffine (XClass W x) = 1 at P and -P.
B. Order at O:
   - construct the projective local ring at O or a normalized infinity
     valuation on W.FunctionField;
   - choose a uniformizer (e.g. x/y) and prove orderAtO x = -2;
   - prove orderAtO (fP) = -2 by fP = X - x(P) and the constant term.
C. Divisor layer:
   - CurveDivisor W := W.Point ->_0 Int;
   - principalDivisor : W.FunctionField^x -> CurveDivisor W from the point orders;
   - prove additivity and then C1; C3 adds the finite product and degree/divisor.
D. C4/C5 still additionally need quotient/multiplication isogenies and pullback
   divisors (section 2.1).

No new Lean file was added for task-96: without A+B the target theorem would
either be conditional on an invented order API or a fake definition; both are
forbidden. The existing Mzk1Route3DivisorActual.lean remains the green partial
file (DONE EXIT=0, 20:24:20Z).


## 8. task-113: affine order infrastructure (partial)

File: tmp/sheaf/xif/paper/Mzk1AffineOrderActual.lean.

### 8.1 Proved/derivable part

- Module.Finite K[X] W.CoordinateRing: W.polynomial is monic in Y;
  Polynomial.Monic.finite_adjoinRoot applies.
- Algebra.IsIntegral K[X] W.CoordinateRing: from the finite module instance.
- Ring.DimensionLEOne W.CoordinateRing: Ring.DimensionLEOne.of_isIntegral
  over K[X], using the PID dimension-one instance for K[X].
- IsNoetherianRing W.CoordinateRing: AdjoinRoot of a monic polynomial over
  K[X] is Noetherian (Mathlib AdjoinRoot Noetherian instance).

### 8.2 Exact remaining gap

The only missing Dedekind condition is integral closedness of
W.CoordinateRing in its fraction field:

  IsIntegrallyClosed W.CoordinateRing.

Mathlib has no theorem that the coordinate ring of a smooth plane cubic is
integrally closed, and no IsDedekindDomain instance for W.CoordinateRing.
Without IsIntegrallyClosed one cannot obtain IsDedekindDomain through
isDedekindDomain_iff. Consequently:
- no IsDedekindDomain instance;
- no HeightOneSpectrum at XYIdeal;
- no HeightOneSpectrum.valuation;
- no orderAtAffine;
- the order-1 vanishing of fP at P is not yet stated in Mathlib terms.

Minimal supplement: prove that W.CoordinateRing is integrally closed (normal)
from smoothness of the Weierstrass cubic. A possible route is:
1. show W.CoordinateRing is a regular local ring at every maximal ideal
   (Jacobian criterion for the smooth plane cubic);
2. use a normal-domain theorem for Noetherian regular rings;
3. or prove the fraction-field integral-closure statement directly via the
   coordinate ring being a Dedekind domain (currently circular).
Mathlib currently has no packaged theorem for steps 1-2 for this coordinate
ring; that is the exact missing API.

### 8.3 Consequence

C1 remains PARTIAL: affine fP, nonzero and the XYIdeal zero-ideal relation are
green; the order-at-P statement and full div(fP) are blocked on the missing
normal/Dedekind step. No fake orderAtAffine is introduced.


### 8.4 Build evidence (task-113)

File: tmp/sheaf/xif/paper/Mzk1AffineOrderActual.lean.
- START 2026-11-12T21:11:32.852Z (final source)
- DONE EXIT=0 2026-11-12T21:11:55.236Z (22s)
- olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1AffineOrderActual.olean
  (size 29360 B, mtime 2026-11-12T21:11:54Z)
- #print axioms:
  coordinateRing_moduleFinite, coordinateRing_isIntegral,
  coordinateRing_dimensionLEOne, coordinateRing_noetherian
  all depend only on [propext, Classical.choice, Quot.sound]; no sorryAx.
- The per-file log retains earlier failed attempts; the final DONE block is
  decisive.

The file proves the Noetherian/finite/integral/dimension part. It deliberately
does NOT assert IsDedekindDomain or orderAtAffine, because IsIntegrallyClosed
W.CoordinateRing remains absent from Mathlib. The exact supplement is: prove
normal/integrally-closed for the smooth plane cubic coordinate ring, then the
HeightOneSpectrum/adic valuation route becomes available.


## 9. P5-B: CoordinateRing IsIntegrallyClosed attempt (task-117)

The only remaining Dedekind condition from task-113 is:
  IsIntegrallyClosed W.CoordinateRing.

Content search result:
- Mathlib has IsRegularRing / IsRegularLocalRing (RingTheory/RegularLocalRing/
  Defs.lean:51,92), and regular local rings are the expected route to normal
  domains.
- Mathlib has NO theorem "Noetherian regular local ring is integrally closed"
  and NO theorem "regular ring is integrally closed".
- Mathlib has NO Jacobian criterion / smooth-plane-cubic-regularity theorem for
  W.CoordinateRing.
- No IsIntegrallyClosed instance for W.CoordinateRing was found.

Therefore no new Lean file was added for P5-B: a conditional "if the coordinate
ring is regular then integrally closed" file would only restate the missing
normal theorem. The exact minimal supplement is:
1. prove W.CoordinateRing is regular (for example by the Jacobian criterion:
   the partial derivatives of the Weierstrass polynomial do not vanish
   simultaneously at any maximal ideal, using W.IsElliptic);
2. prove the Noetherian regular local ring normal theorem (Serre's criterion or
   Mathlib's absent equivalent);
3. derive IsIntegrallyClosed, then HeightOneSpectrum/orderAtAffine as in task-96.

Until steps 1-2 exist, C1's order statement remains blocked; no fake
IsIntegrallyClosed or orderAtAffine is introduced.

Build/status note for P5-A: the conditional normalization identity is green in
tmp/sheaf/xif/paper/Mzk1P5ThetaBridgeActual.lean (DONE EXIT=0
2026-11-12T21:21:34.323Z; axioms only propext/Classical.choice/Quot.sound).
No P5-B Lean file was added because it would only restate the missing normal
theorem.

End of report.
