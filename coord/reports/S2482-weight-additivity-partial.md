# Weight non-strict additivity: actual

## BUILT (EXIT=0)
S2482WeightAdditivityActual.lean (imports v2 infrastructure):
- two_nsmul_max' : 2 • max a b = max (2•a)(2•b).
- max_add_three' : max a b + 3 = max (a+3)(b+3).
- two_nsmul_degree_add_le.
- two_nsmul_degree_add_le_three.
- W_add_le (z w : A) : W (z + w) ≤ max (W z) (W w).
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Still missing
Strict additivity:
  forall z w, W z < W w -> W (z+w) = W w
and hence wt(a*b)=wt(a)+wt(b), phi preserves norm filtration, phi(x)=x, classification.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482WeightAdditivityActual.lean
EXIT=0; SHA256 FF047454B8619DB77399A657A3C3332EC8321001F0A1C31FB393B01072D37670
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482WeightAdditivityActual.olean
olean SHA256: 833CEC872EC08E5E80DA2F8F0768ABE3BCDD623125AE2ADE200D745953EFEE38
axioms: trio