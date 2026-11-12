# S1341: true HDD source E/localEquiv/image/det

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1341HDDSourceFieldsActualOrExact.lean — EXIT=0.

## Read

- S1300HDDHullDetSource (S1300HDDHullDetActual.lean)
- LocalFieldProductHull / LocalFieldProductHullTransport/Blocks
- HullDeterminantLogVolumeReduction
- FinitePadicTensorLogShellRealization (donor referenced by S1300)

## Actual donors

- LocalFieldProductHull.hull, regionModule, integralSpan_eq_hull,
  measure_hull_pos_lt_top, normalizedLogVolume laws: actual local-field hull.
- HullDeterminantLogVolumeFrozenSpec + hullDeterminantLogVolumeFrozenSpec_holds:
  actual finite packet determinant/tensor/rescale/hull-average laws.
- S1300HDDHullDetSource.toS1215: conditional actual construction of the S1215
  lattice from a source with E/localEquiv/image/det.

## Attempted actual E/localEquiv/image/det

Not constructed:
- rank/E: S1215/S1300 require one finite family E independent of the place v
  with E i ≃+* (oneColumnStructure).localField v for every place v.  The
  actual 1-column local fields localField v depend on v; no uniform E exists
  from the current donors.
- image: no actual output-dependent allowed-image family in the source;
  LocalFieldProductHull takes an arbitrary Set as input, it does not supply it.
- compact_closure/nonempty/coordinate_nonzero: all depend on the missing image.
- detData: DetTensorPowerLogVolumeBookkeeping is a bookkeeping interface; only
  the scalar log-degree calibration instance exists, and the file states it is
  not the paper carrier.

## Exact first field

S1341HDDSourceRequired := S1300HDDHullDetSource I
and the exact uniform-field obligation

S1341UniformLocalEquiv rank E :=
  forall v : FinitePlace Q, (i : Fin rank) -> E i ≃+* localField v.

No inhabitant is supplied.  No rank-one/Fin 1/arbitrary Set surrogate.

## Consumer

S1215HDDLocalLattice (I:=I) / SourceSHEHDDCompatibility.hddLocalLattice.
The conditional s1341LatticeOfSource shows what a genuine source would give;
the source itself is the exact first gap.
