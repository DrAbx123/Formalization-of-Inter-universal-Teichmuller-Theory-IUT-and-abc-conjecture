# S2382: arithmetic Frobenius reduction to permBar

Date: 2026-11-03. Layer O; consumer S2217/S2342.

## Actual

Lean:

  tmp/sheaf/xif/paper/S2382ArithFrobDoneActual.lean
  SHA256 62156E7DC019DE100E0E0E6A70865B5B5BBE4636EE3DB4BA64394B32FCB7D9D8
  EXIT=0
  olean SHA256 7968917D3763730214DB64729839BCCA992223136B4A09D7D944BB6C37E8F641
  size 115832
  axioms propext, Classical.choice, Quot.sound.

Theorems:

- s2382_arithFrobAt_reduction:
    Ideal.Quotient.mk P (sigma • a) =
      frobBar p P (Ideal.Quotient.mk P a),
  for H : IsArithFrobAt (O_K) sigma P.
  Uses S2381SmulCommActual.S2381_smulCommClass as local instance,
  AlgHom.IsArithFrobAt.mk_apply H a, then frobBar and
  Ideal.over_def P p.

- s2382_redRoot_smul:
    redRoot f p P hmonic <sigma • a> =
      permBar (f := f) p P (redRoot f p P hmonic a),
  where the root sigma • a is supplied using S2368_rootTransport.
  This is the arithFrobAt reduction transported to redRoot/permBar.

## Exact next missing to S2217Missing

1. Identify the fibres of redRoot with the normalized irreducible factors of
   fbar and prove the multiset of fibre sizes equals factorDegrees (fbar f p).
2. Apply S2217 cycleType_eq_fiber_sizes / orbitSizeMultiset.

Also still needed for the final statement: choose sigma with
arithFrobAt and relate its rootPerm cycle type to permBar via redRootEquiv
(the root-level transport is S2368_rootTransport + S2382_redRoot_smul; the
remaining identification is with rootPerm, whose roots are in L).

## Conclusion

- BUILT: SMulCommClass instance use, arithFrobAt reduction, redRoot/permBar
  compatibility.
- MISSING: factor multiset and rootPerm/permBar multiset identification.
- no fake; no false S2057 data.
