# S1990: normal form of the S1726 affine coordinate ring and the fixed subring

Date: 2026-11-01 (Asia/Shanghai)
Workspace: D:\lean
Scope: S1983 G3, i.e. the lean proposition
`LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual.S1983CoarseQuotientIsAffineLine`.
Status: **EXIT=0. G3 closed.** No axiom, no sorry, no admit, no postulated
quotient, no production definition changed.

## Result

* File: tmp/sheaf/xif/paper/S1990GenusZeroFixedSubringActual.lean
  - 15496 bytes
  - SHA256 976D3813EC771D02F2095F3BB09519FDBE92CADE277FC4E8182B6B93F8A1EA16
  - 375 lines, 0 errors, 0 warnings
* OLean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1990GenusZeroFixedSubringActual.olean
  - 437456 bytes
  - SHA256 EFEA050907ADDA7D26C991F0BE5DED4729AE39D579BF842DEAEF687749795581
* Compile:
  `lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1990GenusZeroFixedSubringActual.olean tmp/sheaf/xif/paper/S1990GenusZeroFixedSubringActual.lean`
  -> EXIT = 0.
  Log: tmp/sheaf/xif/paper/S1990_compile.log (42 lines, 0 error/warning;
  14 #print axioms blocks, only propext / Classical.choice / Quot.sound,
  0 sorryAx).
* OLean import check:
  tmp/sheaf/xif/paper/_S1990OleanCheck.lean
  Log: tmp/sheaf/xif/paper/S1990_olean_check.log
  -> CHECK_EXIT = 0; the theorems below are readable from the olean.

## What is proved

The actual S1726 affine coordinate ring is

  R' = F'[x,y] / (y^2 - (x^3 + (61/64)x^2 - (125/64)x)),

with the involution `S1898CoordEndo` acting by x |-> x, y |-> -y.
The file proves the explicit normal form and then the fixed subring.

### Normal form

`E : MvPolynomial (Fin 2) F' ~= Polynomial (Polynomial F')` sends
`x` to `C X` and `y` to `X` (variable swap followed by
`MvPolynomial.finSuccEquiv` and `MvPolynomial.uniqueAlgEquiv`).
Under E the Weierstrass polynomial becomes

  `g = X^2 - C fpoly`,  `fpoly = X^3 + (61/64)X^2 - (125/64)X`,

and `g` is monic of degree 2.  The main normal-form statements are:

* `S1990_y_sq : y ^ 2 = S1983PolyToCoordinateRing fpoly`
  (the displayed Weierstrass relation in R').
* `mk_eq_normalForm (P) : mk P = S1983PolyToCoordinateRing ((E P % g).coeff 0)
    + S1983PolyToCoordinateRing ((E P % g).coeff 1) * y`
  (existence: division by the monic g).
* `normalForm_unique : p(x) + q(x)y = p'(x) + q'(x)y -> p = p' and q = q'`
  (uniqueness: the remainder of a degree-<=1 form is itself).
* `S1990_normalForm (r) : exists! (p,q), r = p(x) + q(x)y`
  (the direct-sum decomposition R' = K[x] (+) K[x]*y).

The key well-definedness lemma is
`modByMonic_eq_of_mk_eq : mk P = mk Q -> E P % g = E Q % g`.
It uses `Polynomial.modByMonic_eq_of_dvd_sub` with the monic `g`.

### Fixed subring and G3

* `fixed_imp_mem_range (r) (hr : S1898CoordEndo r = r) :
    r in Set.range S1983PolyToCoordinateRing`.
  Proof: write r = p(x) + q(x)y; the involution sends it to p(x) - q(x)y;
  fixedness and normal-form uniqueness give q = -q, hence q = 0 because
  F' = S1720Field is a NumberField (characteristic zero).
* `S1990InvariantSubring_eq_range :
    S1983InvariantSubring = Set.range S1983PolyToCoordinateRing`.
* `S1990CoarseQuotientIsAffineLine : S1983CoarseQuotientIsAffineLine`.
* `S1983CoarseQuotientIsAffineLine_holds : S1983CoarseQuotientIsAffineLine`
  (same theorem under the S1983 gap name).

Thus the reverse inclusion that was missing in S1983 is now proved: the fixed
subring of the actual affine coordinate ring under the elliptic involution is
exactly K[x]; equivalently the coarse quotient of the once-punctured elliptic
curve by +-1 is the affine line.

## Axiom footprint

All 14 `#print axioms` blocks report exactly:

  [propext, Classical.choice, Quot.sound]

No sorryAx, no axiom declaration, no admit.  The `Classical.choice` comes
from the classical instances used by `Polynomial.modByMonic` / quotient
infrastructure; it is in the project's allowed final-closure set.

## Scope / not claimed

* This closes the **coordinate-ring / coarse-quotient** statement G3.
* It does **not** construct the quotient stack [X_F/{+-1}] and does not
  address S1983's G1 (S1964FirstMissing) or G2 (S1983SignatureNotForcedByFiber).
  Those remain exactly as recorded in S1983_report.md.
* No production definition was changed.  S1983_report.md still describes G3 as
  missing; this S1990 report is the newer evidence and supersedes that
  paragraph (integrator should update S1983_report.md / the node registry).

## Version pins (hashes of imported artifacts)

* S1983 source: 7E361BCA34992387407A4D24A6D0674C15FB640EC68BBC1B2F07F5FD7EEF3043
* S1983 olean: F4EE16CE84E234AEA9E7DB2A352494F3780CDC652874B5BFDA72152B967F9152
* S1990 source: 976D3813EC771D02F2095F3BB09519FDBE92CADE277FC4E8182B6B93F8A1EA16
* S1990 olean: EFEA050907ADDA7D26C991F0BE5DED4729AE39D579BF842DEAEF687749795581
