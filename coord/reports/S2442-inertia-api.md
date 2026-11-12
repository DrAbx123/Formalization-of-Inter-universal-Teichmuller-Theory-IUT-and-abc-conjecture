# S2442 inertia API: actual subgroup, normal, quotient

Layer: O (p-adic absolute Galois inertia API).
Source object: LocalAbsoluteGalois p = Gal(PadicAlgCl/Qp).

## BUILT (EXIT=0, actual)
- PadicPrimeToPTorsion: subgroup of units of AlgebraicClosure Qp consisting of elements u with
  exists n, Nat.Coprime n p and u^n = 1.
- PadicPrimeToPAction: actual monoid hom LocalAbsoluteGalois p ->* MulAut(PadicPrimeToPTorsion)
  induced by localGaloisUnitsAction.
- PadicAbsoluteGaloisInertia: kernel of that action (elements acting trivially on all prime-to-p torsion units),
  an actual normal subgroup (instance PadicAbsoluteGaloisInertia_normal).
- mem_PadicAbsoluteGaloisInertia_iff.
- PadicInertiaQuotient := LocalAbsoluteGalois p quotient by inertia; actual group type.
- PadicInertiaQuotientProcyclic: the exact procyclic/Frobenius-lift statement (exists one generator with closure top).

## Exact missing / caveat
- The definition above is inertia via prime-to-p torsion units. For a local field this kernel equals
  ker(G_Qp -> Gal(residue closure/residue)); that equivalence is not proved here (it needs the
  valuation/residue action API and the standard identification). So this file gives an actual inertia
  subgroup API, not the literal residue-kernel definition.
- PadicInertiaQuotientProcyclic is only a Prop, no inhabitant: no Frobenius-lift/procyclic theorem
  in Mathlib/tree. Exact missing: construct a Frobenius lift sigma and prove closure {sigma}=top in
  the quotient (equivalently quotient procyclic).
- No fake axiom/sorry/interface inhabitant.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2442InertiaAPI.lean
EXIT=0; SHA256 B3B2054A3EF011B49A8AD359E2FFAE5FC1C486DADFB00DB5584960C287355E1F
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2442InertiaAPI.olean
olean SHA256: 4289FCB0C4AEC9E8074EC4A134C71B4F77DF0C5EE090F27B25CD9E5B34E17598
axioms: propext, Classical.choice, Quot.sound (no sorryAx).