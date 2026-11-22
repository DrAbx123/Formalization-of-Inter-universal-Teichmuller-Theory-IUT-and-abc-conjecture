# S2766 — 196a1 at l=5: Serre large-image audit

Date: 2026-11-07. Reference/audit only; no Lean actual claim.

## 1. Curve data (LMFDB 196.a1, Cremona 196a2)

LMFDB page: https://www.lmfdb.org/EllipticCurve/Q/196/a/1

```text
y^2 = x^3 - x^2 - 142x + 701
Weierstrass [a1,a2,a3,a4,a6] = [0,-1,0,-142,701]
Conductor N = 196 = 2^2 * 7^2
Discriminant Delta = 784 = 2^4 * 7^2
j = 406749952
CM: no
Rank: 1
Torsion structure: trivial (E(Q)_tors = 0)
```

Isogeny class: https://www.lmfdb.org/EllipticCurve/Q/196/a/

```text
196.a1  [0,-1,0,-142,701]  j=406749952  Delta=784  torsion []  mod.degree=18
196.a2  [0,-1,0,-2,1]      j=1792        Delta=784  torsion []  mod.degree=6
Isogeny matrix (smallest cyclic degree): [[1,3],[3,1]]
```

## 2. Required checks

1. Torsion structure: TRIVIAL.  In particular E(Q)[5] = 0.
2. Rational 5-isogeny: NONE.  The isogeny class has two curves and the
   smallest cyclic isogeny degree between them is 3 (matrix [[1,3],[3,1]]);
   `reducible_primes()` in Sage docs is [3].  A degree-5 rational isogeny would
   give an entry 5, absent.
3. 5 does NOT divide N or Delta:
   N = 2^2*7^2, Delta = 2^4*7^2, so 5 ∤ N and 5 ∤ Delta.

Therefore the local obstruction and the rational 5-torsion/isogeny obstructions
are absent for 196a1 at p=5.

## 3. Sage gal_reps: exact class data

Sage source:
https://github.com/sagemath/sage/blob/develop/src/sage/schemes/elliptic_curves/gal_reps.py

The module docstring contains the exact 196a1 examples:

```text
sage: E = EllipticCurve('196a1')
sage: rho = E.galois_representation()
sage: rho.is_reducible(3)
True
sage: rho.is_surjective(5)
True
sage: rho.reducible_primes()
[3]
sage: rho.non_surjective()
[2, 3]
sage: rho.image_type(5)
'The image is all of GL_2(F_5).'
```

So Sage's class data certifies GL_2(F_5)-surjectivity at p=5 (stronger than
SL_2(F_5) containment).

## 4. Sage `_is_surjective` algorithm (source-derived)

`is_surjective(p, A=1000)` caches `_is_surjective(p, A)`:

1. `T = E.torsion_subgroup().order()`; if `T % p == 0` and `p != 2`, returns
   False with image_type 'meta-cyclic inside a Borel subgroup...'.
2. p=2: use cubic `x^3 + b2 x^2 + 8 b4 x + 16 b6`; rationality/number of roots
   determines trivial/cyclic order 2 or GL2(F2) (or cyclic order 3).
3. p=3: `division_polynomial(3)`; if irreducible and PARI polgalois order 24,
   returns True (GL2(F3)); otherwise False.
4. If E has CM: returns False.
5. p >= 5: set `Np = N*p`; loop over primes ell < A (or 1000); for ell ∤ Np:
   - `a_ell = E.ap(ell)`; if `a_ell % p != 0`:
     - `u = a_ell^2 / ell mod p`; if `u` not in `_ex_set(p)`, set
       `exclude_exceptional_image = True`;
     - `s = kronecker(a_ell^2 - 4 ell, p)`; collect nonzero signs;
   - if both signs +1 and -1 seen AND exceptional image excluded, returns True
     with 'The image is all of GL_2(F_p).'
6. If loop finishes: if `is_reducible(p)` returns False (Borel); otherwise
   returns None (undetermined).

`_ex_set(p)` is the set of trace^2/det values of exceptional subgroups in
PGL2(Fp); for p=5 it is `[0,1,2,4]` (source example).

For 196a1, p=5, the class data says the algorithm reaches True.

## 5. What this gives / what is still missing

Gives:
- exact curve and invariants;
- torsion trivial, no rational 5-isogeny, 5∤N/Δ;
- Sage class-level certificate `is_surjective(5)=True` and image_type
  `'The image is all of GL_2(F_5).'` with exact source citation.

Still missing for the Lean target:
- explicit E[5] basis and Frobenius matrices in a common basis;
- a Lean proof of SL2(F5) <= range; Sage's algorithm works with a_ell traces/
  Kronecker symbols and does not expose representation matrices.

## 6. Verdict

196a1 at l=5 is a good alternative to 37a1: trivial torsion, no rational
5-isogeny, 5∤N/Δ, and Sage documents GL_2(F_5)-surjectivity.  It is still not
a Lean actual proof; explicit matrices remain a separate object gap.  Do not
claim Lean actual or a formal Serre large-image theorem.