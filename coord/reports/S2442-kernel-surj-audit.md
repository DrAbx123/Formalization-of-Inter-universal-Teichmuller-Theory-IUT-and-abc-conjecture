# Residue kernel / surjectivity / Frobenius: exact missing

## Actual baseline
- S2442InertiaAPI.lean: EXIT=0; source SHA B3B2054A3EF011B49A8AD359E2FFAE5FC1C486DADFB00DB5584960C287355E1F; olean SHA 4289FCB0C4AEC9E8074EC4A134C71B4F77DF0C5EE090F27B25CD9E5B34E17598.
  Actual PadicPrimeToPTorsion, PadicPrimeToPAction, PadicAbsoluteGaloisInertia (normal), PadicInertiaQuotient.
- S2442ResidueAction.lean: EXIT=0; source SHA F5F37EF754209450FAF3020037CB5DD92C7992AF55082E062DDD00E2BDF5A27D; olean SHA EE3317CC661A66F9CF3FD020AAC72DC12EDC495C3490F0B3842C9E4D38B6575E.
  Actual PadicValuationSubring, PadicResidueField, PadicValuationSubringAut, PadicResidueAction, PadicResidueKernel (normal).
- Exact Prop surfaces already present: PadicResidueKernelEqualsInertia, PadicResidueActionSurjective.

## (1) Kernel equality: not proved
Both sides are actual normal subgroups. To prove
  PadicResidueKernel p = PadicAbsoluteGaloisInertia p
one needs both inclusions, and each needs a valuation-theoretic API absent from the tree:
- residue-kernel <= prime-to-p inertia: if sigma fixes the residue field, it fixes all prime-to-p
  torsion units. Requires injectivity of reduction on n-torsion for n coprime p (Teichmuller/
  p-adic logarithm; a prime-to-p root of unity in 1 + maximalIdeal is trivial).
- prime-to-p inertia <= residue-kernel: if sigma fixes all prime-to-p torsion units, it fixes the
  residue field. Requires that every residue-field element is the reduction of a prime-to-p root
  of unity (Fpbar is torsion) and a Teichmuller lift/reduction-surjectivity statement.
None of these lemmas is present. No equality or inclusion was proved.

## (2) Surjectivity: not proved
PadicResidueActionSurjective says the residue action reaches all of Gal(Fpbar/Fp).
A proof needs:
- identification of PadicResidueField with the algebraic closure of ZMod p;
- the fact that a compatible Frobenius/automorphism system lifts to an automorphism of PadicAlgCl;
- surjectivity of G_Qp -> Gal(Fpbar/Fp) (decomposition quotient).
Mathlib has finite-field Frobenius but no lift to Qpbar; no such surjectivity theorem in the tree.

## (3) Frobenius lift / procyclic: not constructed
A Frobenius lift sigma : LocalAbsoluteGalois p inducing x -> x^p on the residue field is missing.
Even with sigma, proving closure{sigma}=top in PadicInertiaQuotient requires the kernel equality
and the identification of the quotient with Gal(Fpbar/Fp).
PadicInertiaQuotientProcyclic remains a Prop, no inhabitant.

## Status
No new Lean file compiled; no build/cache. No fake/axiom/interface inhabitant. Exact first missing:
  residue-kernel <-> inertia equality (both inclusions), residue-action surjectivity, Frobenius lift.
These are genuine local-field/valuation API gaps, not syntactic restatements.