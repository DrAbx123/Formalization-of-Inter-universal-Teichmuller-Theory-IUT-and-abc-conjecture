# S1418: consuming the S1402 dependent-place HDD source — actual hull/det, exact first field

Date: 2026-10-31 (Asia/Shanghai)
Lean: `tmp/sheaf/xif/paper/S1418HDDConsumerActual.lean` — **EXIT=0** (`lake env lean`).
SHA256: `AA706C3DEFC39A8CBEEF43274707A9225D59D6649CF073047EEBFC14E22E7313`
Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1418HDDConsumerActual.olean` (292352 bytes).
Axiom probe: `_S1418AxiomProbe.lean` EXIT=0; all key theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

## Consumed

- `S1402DependentHDDSource I s`: `image`, `compact_closure`, `nonempty`,
  `coordinate_nonzero`, `detData`.
- `LocalFieldProductHull.hull / region / unitRegion / integralRing / integralSpan_eq_hull`.
- `DetTensorPowerLogVolumeBookkeeping` and `hullDeterminantLogVolumeFrozenSpec_holds`.

## Constructed actual data (not an arbitrary Set)

1. `S1418GlobalLattice D o := D.dependentHull o`, definitionally the actual
   `LocalFieldProductHull.hull (D.image o)` (`rfl`).
2. `D.image o ⊆ S1418GlobalLattice D o`; nonempty; hull-idempotent; monotone.
3. `∃ lam, (∀ v, lam v ≠ 0) ∧ S1418GlobalLattice D o = region lam`;
   also `= (fun x => lam * x) '' unitRegion`, and the least-region property.
   The closure step is proved without `ProperSpace` (closedness of every
   admissible region + `closure_minimal`).
4. Under the explicit nonarchimedean hypothesis `hna`,
   `Submodule.span (integralRing hna) (closure (D.image o)) = S1418GlobalLattice D o`.
5. `det (x) M` law on the lattice and its two-fold iterate
   (`logVolume (det (det L)) = M * M * logVolume L`); `0 < M`.
6. Place projection `S1418PlaceProjection D o v = {x v | x ∈ lattice}` is exactly
   the actual scaled closed ball `closedBall 0 ‖lam v‖`; it contains zero and is
   nonempty. This is the rank-one `O_v`-lattice content of the source.
7. For `s.Nonempty`, the global lattice is nontrivial (contains 0 and a nonzero point).

## Exact first field

`S1418HDDLocalLatticeRequired I := S1215HDDLocalLattice (I := I)`; **no inhabitant
is asserted**.

Reason: the dependent source's factor at a place is `Completion v` itself
(`s1418DependentE_eq_localField`, `rfl`), while the S1215 lattice at a place is a
set of `Fin rank → Completion v` tuples. The paper's HDD local lattice is the
localization of an arithmetic vector bundle of rank `> 1` (IUT III, Step (xi-d));
Card AV still does not model rank/module/integrality (R3). The source's
per-place projection is exactly a rank-one scaled unit ball, so a rank-one,
constant/diagonal or arbitrary-Set lattice would be a surrogate and is not used.
No new assumption, axiom or `sorry` is introduced.

## Not run

Project build, comparator, independent review. Only the single-file compile and
the local axiom probe were run. `target_accepted = false` (the S1215 first field
remains exact).

## Next executable step

The exact residual is the rank-`r > 1` arithmetic-vector-bundle localization
(rank + local module + integral section family). Once supplied, the S1215
`hddLocalLattice` first field follows; the actual global hull and `det (x) M`
laws proved here then feed the det/log-volume comparison.
