# S1933: prePsi separability by the derivative/gcd certificate — proved for n = 3, exact gap for general n

Date: 2026-11-01 (Asia/Shanghai).  File: `tmp/sheaf/xif/paper/S1933PrePsiSeparableActual.lean`.

## Verification

- Build:
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1933PrePsiSeparableActual.olean tmp/sheaf/xif/paper/S1933PrePsiSeparableActual.lean`
- EXIT = 0, no errors, no warnings, no `sorry`, no `axiom`, no `opaque`.
- Source SHA256: `F87F74C785430681B950D29A9BDA6B3F35DE200D06D695AE462AEA165288A14C`
  (12967 bytes).
- Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1933PrePsiSeparableActual.olean`,
  SHA256 `DAEAE2A36469319691C7CEA2960870589BA94694A00EC46400071ECB48A071C7` (1073752 bytes).
- Import re-check: `tmp/sheaf/xif/paper/_S1933OleanCheck.lean` imports the olean, `#check`s all
  main declarations and re-runs `#print axioms`; EXIT = 0.
- Axiom footprint of all 10 exported theorems: `propext, Classical.choice, Quot.sound` only.

  statement_compiles: yes.  proof_body_checked: yes (kernel).  kernel_closed: yes.
  target_accepted: **no** — `S1366GenericOddPreΨSeparableInput` itself is not inhabited.

## What is proved (unconditional, no detection, no cardinality, no torsion point)

1. `S1933_b8`: `W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4` over a characteristic-zero field
   (from `WeierstrassCurve.b_relation`); this is the only relation between the four b-invariants.
2. `S1933_derivative_Ψ₃`: `(Ψ₃)' = 12X³ + 3b₂X² + 6b₄X + 3b₆`.
3. `S1933_bezout_three` — the explicit derivative/gcd certificate at n = 3:

   12*(b₂² - 8b₂X - 32b₄ - 48X²) * Ψ₃
     + (144X³ + 36b₂X² + (168b₄ - 4b₂²)X + (108b₆ - 4b₂b₄)) * (Ψ₃)'
     = -12 * Δ

   for every Weierstrass curve over every characteristic-zero field.  Found by a symbolic
   extended-Euclidean computation over Q(b₂,b₄,b₆) (with b₈ eliminated by 4b₈ = b₂b₆ - b₄²),
   then kernel-checked by `Polynomial.funext` + generic-point evaluation (char 0 fields are
   infinite) and `field_simp; ring`.
4. `S1933_preΨ_three_separable`: **`(W.preΨ 3).Separable` for every elliptic W over every
   characteristic-zero field.**  This is the first nontrivial case |n| > 1 of the target in the
   tree (S1420 only had n = ±1).  Proof: invert the certificate's right-hand side -12Δ, which is
   nonzero because Δ is a unit on an elliptic curve, and use `separable_def'` (Bezout form).
5. `S1933Certificate n`: the general certificate shape over the universal curve
   `S1933W : WeierstrassCurve (MvPolynomial (Fin 5) ℤ)`,
   `∃ k c A B, c ≠ 0 ∧ A * preΨ n + B * (preΨ n)' = C (c * Δ ^ k)`.
6. `S1933separable_of_certificate`: **a certificate at n gives `(W.preΨ n).Separable` for every
   elliptic W over every characteristic-zero field**, by specializing Z[a₁..a₆] → F
   (`MvPolynomial.eval₂Hom`), `map_preΨ`, `map_Δ`; Bezout is preserved by ring homs, Δ stays a unit.
7. `S1933ExactFirstMissing := ∀ n, ¬ Even n → n ≠ 0 → S1933Certificate n`, with
   `S1933generic_of_certificates` (gives `S1366GenericOddPreΨSeparableInput`),
   `S1933S1906Separability` (gives `S1906Separability l` for every l) and
   `S1933S1906BasisGap` (gives `S1725RankTwoBasisGap l`).
8. `S1933Certificate_one`, `S1933Certificate_neg_one`: the certificate is realisable at n = ±1.

## The exact first missing

For each odd n ≥ 3, an explicit quadruple (A, B, c, k) with

  A * preΨ_n + B * (preΨ_n)' = C (c * Δ^k)   over  Z[a₁,a₂,a₃,a₄,a₆],

i.e. `S1933Certificate n` for all odd n ≠ 0.  This is a finite polynomial identity per n: no
field quantifier, no specializing argument, and by (6) it is exactly the uniform input that
closes the target.  At n = 3 it is `S1933_bezout_three` (k = 1, c = -12).

Equivalent discriminant form.  Since Resultant(f,f') = ±lc(f)·Disc(f) and the resultant lies in
the ideal (f, f') (Sylvester adjugate), the certificate exists as soon as

  Disc(preΨ_n) = c_n * Δ^{k_n},   c_n ∈ Q^×,

with no other irreducible factor.  The b-weight of Disc(preΨ_n) is 2·d(d-1) with
d = (n²-1)/2, while Δ has weight 12, which forces

  k_n = (n²-1)(n²-3)/24        (n=3: 2,  n=5: 22,  n=7: 92),

and the computations below suggest the closed form c_n = (-1)^((n-1)/2) · n^((n²-3)/2).

Numerical evidence (sympy, NOT formalized):
- n = 3: Disc(Ψ₃) = -27·Δ² in the a-presentation (completed-square check: the free-ring
  resultant factors as -81·Q with Q(b(a)) = Δ(a)²).  What is *kernel-checked* at n = 3 is the
  corresponding Bezout form S1933_bezout_three, not this discriminant identity.
- n = 5: in the short normal form (b₂=0, Δ = -16(4A³+27B²)) one gets
  Disc(preΨ₅) = 48828125·16^22·(4A³+27B²)^22 = 5^11·Δ^22, consistent with c₅ = +5^11, k₅ = 22
  (also checked exactly at the single specialization A = B = 1).
This pins the missing input to a single, computer-checkable identity family; nothing in Mathlib
v4.32.2 provides it, and no case n ≥ 5 is formalised anywhere in this tree.

## Why TauCeti cannot be used

The vendored copy `tmp/TauCetiDivisionPolynomialSeparable.lean` proves
`separable_preΨ` exactly by the route excluded here:

- it needs `card_zsmul_fiber` ("[n] is n²-to-one over an algebraically closed field") to get
  `∃ T : Finset, #T = n² ∧ ∀ P, P ∈ T ↔ n • P = 0`, i.e. detection + torsion cardinality;
- it then applies `separable_of_natDegree_le_card_roots` to the two-to-one abscissa count;
- its imports are TauCeti modules (`Torsion.Roots`, `Isogeny.MulByInt.Fiber`,
  `FieldTheory.Separable.OfRootCount`, `DivisionPolynomial.Coprimality`) at Lean v4.36 /
  a newer Mathlib pin; none of them exists in this tree.

So porting TauCeti would import precisely the detection/cardinality bypass that is out of scope.

## Why the derivative/gcd route needs an identity, not a generic-fiber argument

Separability/Squarefree is NOT preserved by specialization or by ring homomorphisms:
X² - t is squarefree over Q(t) but specializes to X² at t = 0.  Therefore

- proving "the generic curve has separable preΨ_n" (e.g. over Q(a₁..a₆)) would NOT give the
  target for a specific curve;
- the property that IS preserved by an arbitrary ring hom is a Bezout identity / IsCoprime,
  which is why the missing input is stated as a certificate over the universal curve.

Two further hard constraints on any proof:

- The three-term EDS recurrences (preΨ_even, preΨ_odd) are uniform in b₂,b₄,b₆,b₈, so they
  alone cannot decide the question: e.g. at Δ = 0 (curve y² = x³, all aᵢ = 0) one has
  preΨ₃ = 3X⁴, which is not squarefree.  The identity must use Δ ≠ 0, which is exactly what the
  certificate's right-hand side c·Δ^k encodes (c ≠ 0, k ≥ 1).  (This curve-level observation is
  a hand computation, not formalised in the Lean file.)
- Mathlib v4.32.2 has no derivative/resultant/discriminant theorem for preΨ_n, no general EDS
  net relation applied to Ψ_n (only the three-term recurrences), and no coprimality theory for
  division polynomials.

## Next executable step

Run the same pipeline that produced `S1933_bezout_three` at n = 5: express preΨ₅ by the
recurrence over Q(b₂,b₄,b₆) (b₈ eliminated), compute `gcdex(preΨ₅, (preΨ₅)')`, clear
denominators (the denominator is ±Res = ±5·Disc, i.e. a constant times Δ^22), write the
resulting A, B with `C (c * W.Δ ^ 22)` as in section 2, and prove the identity with
`Polynomial.funext; eval; field_simp; ring` exactly as `S1933_bezout_three`.  The certificate
size grows (A has x-degree ≤ 10 at n = 5), so `ring` cost is the main risk.

## Relation to earlier reports

- S1380 concluded "first missing = TauCeti's separable_preΨ"; the vendored TauCeti source is now
  known to be the counting route, and the present file provides an alternative formulation
  (certificate) plus a proved instance.
- S1420 proved the reformulations (Separable = IsCoprime = Bezout = Squarefree, pointwise
  derivative form) and n = ±1; it did not prove any n with |n| > 1.
- S1924 removed detection/zero criterion from the S1906 route; combined with this file the S1906
  basis gap now follows from `S1933ExactFirstMissing` alone.
