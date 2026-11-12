# S1942: the derivative/gcd certificate for prePsi_5, and separability at n = 5

Date: 2026-11-01 (Asia/Shanghai).  File:
`tmp/sheaf/xif/paper/S1942PrePsiFiveActual.lean`.

## Verification

- Build:
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1942PrePsiFiveActual.olean tmp/sheaf/xif/paper/S1942PrePsiFiveActual.lean`
- EXIT = 0; no errors, no warnings, no `sorry`, no `admit`, no `axiom`, no `opaque`.
  (The only output of the build is the four `#print axioms` lines listed below.)
- Source SHA256: `9F01ECC7B28D17B796F200C8FBD1114EFEF1B7D073E3F47979303C68B9EF70E5`
  (28518 bytes).
- Olean:
  `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1942PrePsiFiveActual.olean`,
  SHA256 `0921C5AB51A8AECE86E75E9D263560B22C5E38984EFBB5D3C128F39A4A85168A`
  (166508736 bytes).  The olean is large because the `ring` proof term of the
  scalar identity is large; the definitions themselves elaborate to a 539 KB olean.
- Import re-check: `tmp/sheaf/xif/paper/_S1942OleanCheck.lean` imports the olean,
  `#check`s all main declarations and re-runs the axiom prints; EXIT = 0.
- Axiom footprint of all four exported theorems:
  `propext, Classical.choice, Quot.sound` only.

  statement_compiles: yes.  proof_body_checked: yes (kernel).
  kernel_closed: yes.  target_accepted: the two requested targets are closed;
  no `S1933Certificate` hypothesis remains in the separability theorem.

## What is proved

1. `S1942_preΨ_five`: the n = 5 recurrence
   `W.preΨ 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3`, from Mathlib's
   `WeierstrassCurve.preΨ_odd 2`.
2. `S1942A` and `S1942B`: explicit polynomials in
   `W.b₂, W.b₄, W.b₆` with 218 and 249 monomials respectively (after
   removing the content `20^55 * 5^11` and seventeen powers of
   `Delta_b = 4 * Delta`).  They were found by the extended Euclidean
   algorithm over Q(b₂,b₄,b₆) with b₈ eliminated by
   `4*b₈ = b₂*b₆ - b₄^2`.
3. `S1942A_map`, `S1942B_map`: A and B commute with coefficient
   extension, used in the universal descent.
4. `S1942_bezout_five`: for every Weierstrass curve over every
   characteristic-zero field,

   `S1942A W * preΨ 5 + S1942B W * (preΨ 5)' = C (5120 * Δ^5)`.

   Proof: `Polynomial.funext` at a generic point, unfolding the
   recurrence, eliminating b₈ with `S1933_b8`, then
   `field_simp; ring`.  No detection, no torsion count, no
   cardinality.
5. `S1942Certificate_five : S1933Certificate 5`: the universal
   certificate with `k = 5`, `c = 5120`,
   `A = S1942A S1933W`, `B = S1942B S1933W`.
   Proof: specialise the field identity along
   `Z[a1..a6] -> FractionRing (MvPolynomial (Fin 5) Z)`, rewrite
   with `map_preΨ`, `map_Δ`, `S1942A_map`, `S1942B_map`, and
   descend along the injective structure map with
   `Polynomial.map_injective`.
6. `S1942_preΨ_five_separable`: for every elliptic Weierstrass curve
   over every characteristic-zero field, `(W.preΨ 5).Separable`, obtained
   from `S1933separable_of_certificate W S1942Certificate_five`.

## Route note

The computation was done with a 12x12 Bezout matrix over a finite field, CRT
reconstruction over 61 primes, exact integer verification of

  `A * P16 + B * (P16)' = 320 * Delta_b^5`

with `P16 = 64 * preΨ_5`, and then division by the common content
`20^55 * 5^11` and by `Delta_b^17`.  The final identity is
the small one stated above.  The source file contains no trace of TauCeti,
detection, cardinality or torsion-point counting.
