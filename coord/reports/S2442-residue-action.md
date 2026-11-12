# S2442 residue action API: actual

Layer: O (residue action of LocalAbsoluteGalois p).

## BUILT (EXIT=0, actual)
- PadicValuationSubring := valuationSubring of Valued.v on PadicAlgCl p.
- PadicResidueField := IsLocalRing.ResidueField of that valuation subring.
- PadicAlgCl_norm_map: every sigma in LocalAbsoluteGalois p preserves the spectral norm (via spectralNorm_eq_of_equiv).
- PadicAlgCl_valuation_map_eq: sigma preserves Valued.v.
- PadicValuationSubringAut: actual ring automorphism of the valuation subring induced by sigma.
- PadicResidueAction: actual monoid hom LocalAbsoluteGalois p ->* RingAut (PadicResidueField p), via IsLocalRing.ResidueField.mapAut.
- PadicResidueKernel: kernel of the residue action, an actual normal subgroup.
- PadicResidueKernelEqualsInertia and PadicResidueActionSurjective: exact Prop surfaces (not inhabited).

## Exact missing
1. PadicResidueKernelEqualsInertia: kernel of residue action equals the prime-to-p torsion inertia
   (S2442InertiaAPI.PadicAbsoluteGaloisInertia). This needs the valuation/residue action and the
   standard identification of inertia; not proved.
2. PadicResidueActionSurjective: residue action surjects onto Gal(Fpbar/Fp) (procyclic Zhat).
   No Frobenius lift/surjectivity theorem in Mathlib/tree.
3. Consequently PadicInertiaQuotientProcyclic remains a Prop.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2442ResidueAction.lean
EXIT=0; SHA256 F5F37EF754209450FAF3020037CB5DD92C7992AF55082E062DDD00E2BDF5A27D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2442ResidueAction.olean
olean SHA256: EE3317CC661A66F9CF3FD020AAC72DC12EDC495C3490F0B3842C9E4D38B6575E
axioms: propext, Classical.choice, Quot.sound (no sorryAx).