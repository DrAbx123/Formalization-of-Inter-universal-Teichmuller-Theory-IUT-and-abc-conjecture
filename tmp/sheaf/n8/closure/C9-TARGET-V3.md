# C9 target v3 (stage-1 lock candidate, not Lean)

Date 2026-10-23. Based on C9-STAGE1-SUPPLEMENT-ROUTE-20261023.md.
Status: TARGET UNDER REVISION; no implementation until accepted.

## Input

- Actual native qualified initial Theta data `S` (SourceNativeInitialThetaData).
- Actual log-theta-lattice `L` over `S`; full Lean type of `L` remains a statement gap.
- Selected places `V(S)` are a section over the Fmod places; do not use arbitrary old `OriginalInput`.

## Consistency corrections (2026-10-23 review)

- Adm: require almost-everywhere zero local normalized log-volume, not pointwise equality to a reference unit region.
- Readout: define per-framework `ell_f` first; native q and algorithm output have independent definitions, then compare after reference calibration/column shift.
- Distinguish RawPoss pre-regions, component unions U_i, hulls H_i, and admissible regions HullPoss; do not identify them.
- Ind1/2 give invariance of the corresponding normalized readout; Ind3 gives one-sided control; hull enlargement and global equal-volume replacement are separate.
- Global equal-volume replacement must preserve `A ⊆ phi(P) ⊆ phi(H)=H`.
- P6 primary task is the source double-construction comparison on the actual q-pilot, not upper-bound transfer; transfer/epsilon are corollaries.
- WithTop only after excluding zero-mass/-infinity and establishing extended readout; Theta finiteness still required.

## Frozen mathematical objects (paper semantics)

1. `alpha`: one complete source-allowed choice, including places, tensor packet, procession components and Ind data; `j` is only a component index, not a full pilot.
2. `R_alpha`: the output region family in the target holomorphic structure, indexed by local places/tuples/procession; a source representation relation must be defined before identifying sets.
3. `U = union_alpha R_alpha`; `H = paperHolomorphicHull(U)`.
4. `Adm(R)`: admissible region conditions (measurability, positive finite mass, local integral/radial structure, global almost-everywhere reference unit); not merely nonempty.
5. `L(R)`: same global signed procession-normalized log-volume; reference regions positive finite; no arbitrary Set full-function log.
6. `HullPoss = {R | Adm(R) and R subset H and R allowed by Step4 enlargement}`; `Values = {L(R) | R in HullPoss}` with region provenance.
7. `Q = L(Rq)` for independent actual q-pilot representation `Rq`; `Theta = L(H)` in WithTop Real, proven finite.

## Acceptance

- P2 normalization/L defined on Adm regions.
- P3 H constructed, admissible blocks positive finite, Theta finite.
- P4 Values bounded: forall z in Values, z <= Theta.
- P6 Q realized or one-sided approximated by allowed outputs: Q in Values, or forall epsilon>0 exists R in HullPoss with Q-epsilon <= L(R).
- P7 from boundedness + realization: Q <= Theta.
- x: determine its source-configuration meaning and prove invariance/faithfulness; do not claim a paper dependence merely from variable use.

## Not accepted as target evidence

- QPaper qPilotRegion = singleton(C3.tensorUnit) and qPilotLogVolume = localSignedLog C3.q; no region-volume identification.
- C9ValuesPaper finite point image over D.Choice; non-atomic Haar mass zero, not admissible.
- ThetaPaper free thetaToC6 map; ValuesPaper arbitrary provenance/subsets; C6 arbitrary B without IsActual.
- Old QSigned/ThetaSigned/Values and their named sorries.

## P0-P7 task decomposition

- P0 source input/index; P1 complete output/representation; P2 unified normalization; P3 source hull/finiteness; P4 enlarged regions/bound; P5 equal-volume/determinant calibration; P6 q input realization/approximation; P7 numeric close.

## Next executable task

P0/P1 source-object table only: list input/output objects, columns/rows, local/tuple/j indices, unit/value-group parts, arrows, allowed Ind, source locations, and existing declarations. No Lean proof until this target is accepted.

## Binding guard (2026-10-24)

Legacy C10 closure (`N8ClosureFull`) and old Layer0/Layer1 closures MUST NOT be reported or consumed as paper N8 closure. See `coord/CLOSURE-GUARD.md`. Only C9-TARGET-V3/P6 target acceptance may be called paper N8 closure.
