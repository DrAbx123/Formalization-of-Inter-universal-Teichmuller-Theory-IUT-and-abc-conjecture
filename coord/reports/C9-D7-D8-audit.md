# C9 D7/D8 audit + D8 cusp actual

## New actual
S2555D8CuspidalDecompositionActual.lean EXIT=0:
- S2555CuspidalDecomposition: for any OrbicurveFundamentalGroupData groups and cusp, constructs
  OrbicurveCuspidalDecompositionData groups (cusp := cusp, subgroup := top, surjectivity proved).
- S2555SourceClauseF: constructs SourceClauseF from exactly (O : TorsionQuotientBoundaryOrigin,
  basis equality, cusp equality); cusp_decomposition is constructed, not assumed.
Axioms trio; no sorryAx.

## Audit
D7: actual constructor d7 from SourceInitialThetaData (Definition31D0D11FromSource, olean actual, no sorry).
D8: actual constructor d8 from SourceInitialThetaData (same file); D8Root lemmas actual conditional on ClauseF.
D8 ClauseF now reduced to: boundary_origin + basis equality + cusp equality.
Remaining D8: actual TorsionQuotientBoundaryOrigin and basis/cusp equalities; S1889 identifies paper cusp datum with TorsionQuotientBoundaryOrigin and first missing as S1881 D9 slot first field C_F.
Epsilon tail: SourceCuspClause real epsilon/cuspScale has no geometric-to-real map; NativeCuspProof lists exact primitives.

C9: C9QPilotRegion actual; C9PaperClosure/P6Closure still have named sorries:
paperC9Comparison, paperC9Output_nonempty, p6SourceClosure_nonempty.
Missing source objects: GlobalLqDonor, P6Readout (Theta/Values); frozen P6Readout refuted for archimedean place.

No fake.