# SourceInitialThetaTuple / clauses A-F: field-by-field status

## Actual arithmetic input
S2482QiArithmeticActual.arithmeticData : InitialThetaArithmeticData 5 over F=Q(i), with actual curve y^2=x^3-x.
S2482QiCurveActual: S2482Curve.IsElliptic, S2482PuncturedCurve.
S2480QiActual: F=AdjoinRoot(X^2+1), HasSqrtNegOne.

## SourceInitialThetaTuple fields
- fbar : SourceFbarExtension A: ACTUAL candidate `SourceFbarExtension.canonical A`.
- source : SourceSignQuotientData A: MISSING. This is the core source stack package; no constructor from `InitialThetaArithmeticData` alone.
- xF : HyperbolicOrbicurve A.F: MISSING (comes from source.xF).
- xF_eq_source: MISSING (depends source).
- cK : HyperbolicOrbicurve A.K: MISSING (comes from source.cK).
- cK_eq_source: MISSING.
- V : Set (NumberFieldPlace A.K): MISSING (source.V; requires place section/selection).
- V_eq_source: MISSING.
- V_mod_bad : Set (NumberField.FinitePlace A.Fmod): MISSING (source.V_mod_bad; needs nonempty odd-residue finite places).
- V_mod_bad_eq_source: MISSING.
- epsilon : OrbicurveBoundaryCusp cK: MISSING (needs actual cK and boundary cusp).
- epsilon_eq_source: MISSING.

## SourceSignQuotientData: exact missing fields
xF, xF_geometry, ellipticInvolution, ellipticInvolution_squared, unique_elliptic_involution, signAction, signAction_inversion_eq_ellipticInvolution, cF, quotient, quotientWitness, xFGroups, cFGroups, fGroupInclusion, xK, cK, xKExtension, cKExtension, xKType, cKType, xK_eq_extension, cK_eq_extension, V, V_mod_bad, V_mod_bad_odd_residue_characteristic, V_mod_bad_nonempty, V_section, V_eq_section, V_mod_bijection, V_place_comap, epsilon.
No inhabitant is constructed in the tree; the conditional bridge `SourceCompletion.toSourceSignQuotientData` consumes a `SourceCompletionSignQuotient`, which itself has no actual input-free constructor.

## Clauses A-F: exact missing fields
### A (field, curve, solvable extension)
- stable_reduction_nonarchimedean: for all finite places of A.F, A.curve.HasStableReductionAt p.
- field_of_moduli: SourceFieldOfModuli A.
- maximal_solvable_extension / property / universal property: needs actual maximal finite solvable Galois subextension of A.Fmod in A.F.
None is constructed; in particular stable reduction at every finite place is not available for the chosen curve.

### B (bad places, Tate comparisons)
- multiplicative_over_bad; q_comparison with `SourceTateComparisonWitness` (FinitePlaceQCandidate + TateCurveComparison + order coprime); residue_characteristic_prime_to_l.
No actual bad place set/Tate parameter is constructed.

### C (torsion representation, kernel field)
- torsion23_rational; torsion_basis; representation; representation_eq_canonical; image_contains_SL2; kernel_field_identification and range equality.
Requires actual rank-two l-torsion basis, GL2 representation, and identification A.K with the kernel field; missing.

### D (K orbicurves, covers, fundamental groups)
- k_signAction, k_quotient, k_quotientWitness, k_quotientExtension, k_quotient_map_eq_extension, k_l_torsion_cover, k_l_torsion_cover_map_eq_quotient, x_groups, c_groups, group_inclusion, x_to_F_groups, c_to_F_groups.
All depend on actual K-side orbicurves/groups; missing.

### E (selected subset, local diagrams)
- selected_eq_V; selected_equiv; finite_local/infinite_local SourceFiniteLocalSource/SourceInfiniteLocalSource for every selected place.
Requires the clause D data and local Galois/curve comparison data; missing.

### F (cusp, boundary, sign)
- boundary_origin : TorsionQuotientBoundaryOrigin l A S.cK; quotient_basis_eq_k_torsion_basis; boundary_cusp_eq_epsilon; cusp_decomposition; cusp_decomposition_cusp_eq_origin.
Requires actual cK orbicurve, torsion quotient boundary, and cuspidal decomposition; missing.

## Conclusion
The tuple is not constructible from `InitialThetaArithmeticData 5` alone: `SourceSignQuotientData` and clauses A-F encode independent source data (orbicurves, sign quotient, reductions, Tate parameters, torsion bases, local groups, boundary cusp). The exact first missing in dependency order is `SourceSignQuotientData A`; before it, actual `xF`/`cF`/`cK` orbicurves and the sign action/quotient witness. No fake/interface inhabitant was added.

No new Lean file compiled; no build/cache command. The actual curve/arithmetic-data results remain S2482QiCurveActual and S2482QiArithmeticActual.