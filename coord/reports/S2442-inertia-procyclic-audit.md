# Inertia quotient: procyclic/Frobenius exact missing

## Actual baseline (already compiled)
S2442InertiaAPI.lean: EXIT=0; source SHA256 B3B2054A3EF011B49A8AD359E2FFAE5FC1C486DADFB00DB5584960C287355E1F; olean SHA256 4289FCB0C4AEC9E8074EC4A134C71B4F77DF0C5EE090F27B25CD9E5B34E17598; axioms propext/Classical.choice/Quot.sound.
Contains actual `PadicPrimeToPTorsion`, `PadicPrimeToPAction`, `PadicAbsoluteGaloisInertia` (normal), `mem_PadicAbsoluteGaloisInertia_iff`, `PadicInertiaQuotient`, and the Prop `PadicInertiaQuotientProcyclic`.

## Why procyclic is not proved
Definition used: inertia = kernel of the action on all prime-to-p torsion units of AlgebraicClosure Qp. This gives an actual normal subgroup and actual quotient.
To prove `PadicInertiaQuotientProcyclic` one needs:
1. the residue map G_Qp -> Gal(Fpbar/Fp) and the identification of its kernel with `PadicAbsoluteGaloisInertia`;
2. surjectivity of that residue map (the quotient is procyclic Zhat);
3. a Frobenius lift sigma : LocalAbsoluteGalois p whose image topologically generates the quotient;
4. closure{sigma}=top in the quotient.
Mathlib/tree has none of these: no residue action of the absolute Galois group on the residue field, no Frobenius lift for Qp, no procyclic inertia quotient theorem. The only Frobenius API in Mathlib is for number-field residue fields/prime ideals (arithFrobAt), not a lift to Qpbar.

## Exact first missing API
A residue-field Galois action and kernel identification:
  def residueAction : LocalAbsoluteGalois p ->* MulAut (AlgebraicClosure (ZMod p))
  theorem residueAction_ker : residueAction.ker = PadicAbsoluteGaloisInertia p
then a Frobenius lift `sigma` and `closure {sigma} = top` in `LocalAbsoluteGalois p / inertia`. None is inhabited.
The current `PadicInertiaQuotientProcyclic` remains a Prop, not actual.

## Status
No procyclic theorem was constructed or refuted. No fake Frobenius lift/axiom/interface inhabitant was added. The actual deliverable remains the inertia subgroup/normal/quotient API above.