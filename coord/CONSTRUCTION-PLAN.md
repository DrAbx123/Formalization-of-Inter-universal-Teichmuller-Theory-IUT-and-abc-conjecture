# Construction plan: no ready object -> construct object (2026-10-24)

Rule: every constructed object must be built from actual production data; no arbitrary field, no empty/terminal degenerate object, no target-as-definition.

## C1. Etale stack / orbicurve
Target: `EtaleStackInstanceSupply F` + `Iut.HyperbolicOrbicurve F`.
Available actual: `schemeRepresentableEtalePseudofunctor` from an actual `SchemeOverField F`; `realizedHyperbolicOrbicurve` given fiber+IsStack+hyperbolic signature.
Construction route: actual representable pseudofunctor associated to a concrete scheme over F; prove IsStack for etale topology (representable presheaf is a stack); nonempty/nonterminal. Then realize once-punctured-elliptic signature.
Missing if any: etale-subcanonicity/stack instance for representable pseudofunctor; concrete scheme (curve) over F.

## C2. D7b local-group section supply
Target: `D7LocalGroupSectionSupply` fields (carriers, pointwise bijective section, finite/infinite data).
Available actual: D7a canonical place-section layer.
Construction route: actual local group carriers from completion units/Galois groups; define section pointwise; prove bijection from existing local group equivalences.

## C3. Cusp datum D8
Target: `SourceCuspClause` actual fields (selected cusp, nonzero quotient, canonical generator, sign ambiguity, Real epsilon/cuspScale, compatibility).
Construction route: actual curve/cusp from arithmetic data; generator from uniformizer; epsilon/cuspScale from actual q/cusp scales.

## C4. D9 compatibility
Target: five arithmetic compatibility (Prop, proof) pairs.
Construction route: instantiate each Prop with the actual equality/containment it encodes and prove from existing arithmetic/source theorems.

## C5. SourceDefinition31Data packaging
Target: actual `SourceDefinition31Data` from C1-C4 + arithmetic/reduction/torsion data.
Route: `StageConstructionTrace.toSource`; no arbitrary Prop/proof fields.

## C6. SourceAllowedOutput J
Target: `P6Comparison.SourceAllowedOutput X`.
Route: `P6BridgeDonors` + C2/C3/C4/T11/C6 actual package; `sourceAllowedOutputOfActualData`.
Missing bridge: `NativeOldC1Bridge` from native root; construct `P6BridgeDonors` (input donors + place binding donors) from C5 and actual native places.

## C7. O3 comparison object
Target: actual `O3ComparisonData` h,A,Z,d,kappa,S.
Route: h from actual tensor hull/nnLattice volume; Q actual; A,Z from actual tensor-edge lattice indices/divisors; prove model law and S>=0. No arbitrary constants.

## C8. O4 target alignment
Target: `SourceAllowedOutput.ellOut = hullUnitLogVolume` / actual Theta.
Route: construct J with `J.region=canonicalHull`, C6NormalizationLink, finrank=1 actual conditions; or construct source hull via images and prove equality.

## C9. O2 eta identification
Target: `etaPilot = ofAdd(etaRssAtFPlace.logVolume)`.
Route: construct actual source etaAnab log-volume from log-shell/region data and prove both sides equal q log-volume; no target-as-definition.

## Status
Construction wave dispatched to transport/primespine/logdescent/iplsheapt/kummer. Results will be recorded per object; only successful actual constructions reduce O1-O6.
