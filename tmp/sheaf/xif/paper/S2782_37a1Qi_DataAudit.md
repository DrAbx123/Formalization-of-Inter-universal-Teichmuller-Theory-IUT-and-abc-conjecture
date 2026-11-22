# S2782 — 37a1 over Q(i): Sage data audit and Lean data checklist

Date: 2026-11-07. Data audit; no Lean actual claim.

## 1. Exact Sage run

WSL command:

```text
wsl -d Ubuntu-24.04 -- /opt/miniconda/envs/sage/bin/sage
Sage 10.9
```

Script: `_S2782_37a1Qi.sage`

```sage
K.<i> = QuadraticField(-1)
E = EllipticCurve([0,0,1,-1,0]).change_ring(K)
```

Output:

```text
conductor Fractional ideal (37)
disc 37
j 110592/37
torsion_order 1
rank 1
cm False
surj5 True
non_surj []
reducible []
local data: two primes above 37, reduction type bad non-split multiplicative,
  Kodaira I1, Tamagawa 1, minimal discriminant valuation 1, conductor exponent 1
(all other places good)
```

So 37a1/Q(i):

- semistable: YES (good everywhere except the two primes above 37, both I1
  nonsplit multiplicative);
- non-CM: YES (has_cm() = False);
- torsion: TRIVIAL (torsion_order = 1);
- rank: 1;
- mod-5 image: Sage number-field galois_representation().is_surjective(5)
  = True; non_surjective() = [], reducible_primes() = []; hence the image
  is GL2(F5) at the class level (Sage algorithm, not explicit matrices).

## 2. Exact vs missing

Exact Sage data are numerical/class-level.  Sage number-field
GaloisRepresentation has no image_type method in this version; the
surjectivity algorithm still returns True.  No explicit E[5] basis or
Frobenius matrices are produced by this run.  Do not fabricate them.

## 3. Lean data checklist for S2782

1. Base field:
   K = GaussianField = QQ(i), NumberField with Gaussian integers.
2. Curve:
   S2782Curve : WeierstrassCurve K := (WeierstrassCurve.mk 0 0 1 (-1) 0).baseChange K
   (37a1: y^2 + y = x^3 - x).
3. Ellipticity: instance S2782Curve.IsElliptic; discriminant = 37.
4. Punctured elliptic curve S2782 : PuncturedEllipticCurve K.
5. Semistability: for every finite place P, good reduction or multiplicative
   reduction; bad places exactly the two primes above 37, each I1 nonsplit;
   Mathlib currently has no general number-field reduction API, so this needs
   a new reduction-type interface or an explicit local model at 37.
6. Non-CM: no IsCM predicate in Mathlib; record as j = 110592/37 and cite
   Sage has_cm False, or define a CM predicate and prove negation.
7. Torsion: Nat.card (S2782.LTorsion 1?) or E(K)_tors = 0; Sage
   torsion_order = 1.  A Lean proof needs a torsion/rank API.
8. mod-5 image:
   - E[5] basis: (Fin 2 -> ZMod 5) ~= S2782.LTorsion fiveLabel;
   - galoisLTorsionMatrixRepresentation;
   - Sage says surjective, but Lean target needs SL2 containment:
     SL2(F5) <= range representation.
9. Explicit Frobenius matrices: not available from this Sage run (no basis/
   matrices).  Do not fill with fake matrices.

## 4. Verdict

- 37a1/Q(i) is semistable, non-CM, torsion trivial, mod-5 surjective at
  Sage class level.
- Lean data checklist above; missing reduction/CM/torsion API and explicit
  E[5] basis/matrices.
- No Lean actual claim; no fake matrices.