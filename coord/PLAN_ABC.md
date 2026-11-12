# ABC / Cor 3.12 prerequisite DAG (planned 2026-11-07)

## Phase A — prerequisites only (no assembly yet)

A1 line-bundle normalized region
  owner: logdescent
  deliver: S2792NormalizedLineBundleBridge
  depends: S2780, S2752, S2743 support absNorm
  acceptance: EXIT=0, olean, axioms trio, no sorry
  content: degree-normalized regionVolume = (1/[K:Q]) * S2736 log volume;
           prove regionWeightGap actual (f_p <= 2 for K=Q(i));
           do NOT claim height gap.

A2 height inequality on paper lambda(point)*O
  owner: transport
  deliver: S2791HeightGapActual (or exact obstruction)
  depends: S2760 paper factor scaling, S2756 fundamental domain, S2781 pointed region
  acceptance: actual height gap on the point-dependent region, or exact missing object.
  content: construct lambda(point)*O with volume growing with point;
           prove height <= (1+eps)*regionVolume directly; no "ABC-hard" escape.

A3 real HyperbolicOrbicurve + sign data
  owner: multiradial
  deliver: S2789E37OrbicurveSignActual
  depends: S2786 37 places
  acceptance: actual constructors, no degeneratePointFiber, no PUnit/True.
  content: xF/xF_geometry/ellipticInvolution/cF/signAction/quotient/groups/xK/cK/epsilon.

A4 F6 = Q(i,E[6])
  owner: volumedet
  deliver: S2790F6Actual
  depends: E37Qi (S2782), S2771
  acceptance: actual NumberField/Algebra/FiniteDimensional/IsGalois + Torsion23Rational.
  content: use IntermediateField.adjoin of all E[6] coordinates; avoid explicit polynomial if possible.

A5 37 places + 8-field block
  owner: qside
  deliver: S2786E37PrimeIdealsActual extension / S2786PlaceBlockActual
  acceptance: two Gaussian primes above 37, singleton SourcePlaceSelection, 8 place fields actual.
  content: 37 = (6+i)(6-i) in Z[i]; construct height-one spectra and place data.

A6 37 multiplicative
  owner: primespine
  deliver: S2794Multiplicative37Actual
  acceptance: actual HasMultiplicativeReduction at both places over 37.
  content: v37, IsUnit 48, valuation Delta<1, valuation c4=1, IsMinimal, HasMultiplicativeReduction.

A7 field_of_moduli + maximal solvable Q -> Q(i)
  owner: kummer
  deliver: S2793FieldOfModuliQiActual
  acceptance: actual SourceFieldOfModuli and maximal_solvable_extension for Fmod=Q, F=Q(i).
  content: E37Qi.j=110592/37; maximal_solvable=top; FiniteDimensional/IsGalois/IsSolvable/le_top.

A8 compile/probe
  owner: iplsheapt
  content: compile A1-A7 as they land; report src/olean SHA and axioms.

## Phase B — assembly (only after A1-A7 actual)

B1 line-bundle ABC bridge
  owner: logdescent
  depends: A1 + A2
  deliver: S2795LineBundleABCBridgeActual

B2 ClauseA
  owner: primespine
  depends: S2782 good outside 37, A6, A7
  deliver: S2796ClauseA37Actual

B3 ClauseC
  owner: qside
  depends: A4 F6, S2784 K37, S2783 base-change large image
  deliver: S2797ClauseC37Actual

B4 ClauseD/E/F
  owner: multiradial
  depends: A3, A5, B2, B3
  deliver: S2798ClauseDEFActual

B5 SourceClauseAssembly / SourceCompletion / T
  owner: lead + owners
  depends: B2-B4
  deliver: final T / then bridge.

## Rule
- No assembly before prerequisites compile actual.
- No PUnit/True/degenerate surrogate.
- Each deliverable must report EXIT, src SHA, olean SHA, axioms.
- If a prerequisite is impossible, report exact obstruction and stop dependent work.

## Status 2026-11-07 (A8 audit)

- A1-A7: NO accepted artifacts yet. Some files have stale/partial oleans; not accepted.
- S2792 (A1): needs `0 <= eps`; current first error: `linarith` with `1 + eps < 0`;
  source is newer than olean (stale).
- S2789 (A3): errors `Field GaussianField` synth failure, `unknown fiveLabel`, and
  missing geometry; sorry warning present.
- A2 S2791HeightGapActual: in progress by transport.
- Rule unchanged: no assembly claims before prerequisites compile.

## Search records 2026-11-07

- Sign quotient: `SourceSignQuotientGeometricCore` / `toSourceSignQuotientData`
  already exist in `SourceDefinition31SignQuotientSupplyReduction.lean`;
  field-units reduction in `SourceGeometricCoreFieldUnitsReduction.lean`.
- Places: `S2786PlaceSelection` reusable (`S2786PlaceBlockActual.lean:44`).
- F6: `EllipticTorsionConsumerWiring.divisionField_finiteDimensional_of_odd_torsion`
  (`LeanFormal/IUT/ABCBridge/Galois/EllipticTorsionConsumerWiring.lean:84`).
- Representable pseudofunctor: external reference
  `tmp/external/promachina-iut-lean-latest/Iut/Foundations/Orbicurve.lean:181`;
  in-tree geometric material O1GeometricOrbicurve / S1419.
- These are reusable records; no new assembly claim.