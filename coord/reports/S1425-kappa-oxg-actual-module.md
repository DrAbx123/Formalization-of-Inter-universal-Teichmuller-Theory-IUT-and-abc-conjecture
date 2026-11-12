# S1425: actual inhabitant of the S1399 paper O^x(G) module/action

Date: 2026-10-31 (Asia/Shanghai)
Lean: tmp/sheaf/xif/paper/S1425KappaOxGActual.lean
SHA256: 363D3D12C6E20B5D4B585E04F575397EA4867245B84D4D270938C3A6C907CEC2
Size: 11505 bytes, 262 lines; no sorry/admit/axiom/native_decide.
Compile: `lake env lean -j1 -R D:/lean tmp/sheaf/xif/paper/S1425KappaOxGActual.lean` EXIT=0
Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1425KappaOxGActual.olean`
built in the same way (`-o`), EXIT=0, 156152 bytes. The first olean attempt
failed on a transient toolchain read (`Init/Data/List/TakeDrop.olean`); the
source itself compiled EXIT=0 both before and after.

## Actual construction (no self/refl, no finite model, no axiom)

S1399 left the paper `O^x(G)` first field as an uninhabited structure.  S1425
inhabits it on actual data from a second actual member of the same Hodge-theater
family:

* `S1425RefStrip I = I.primeStripAt 1 0` — the actual F-prime-strip at lattice
  point (1,0); `S1425MidStrip I = I.primeStripAt 0 1 = S01`.
* `S1425RefLink I = I.primeStripLinkAt 1 0 0 1` — the actual Hodge-theater
  link (1,0) -> (0,1) at the F-prime-strip level, an actual
  `FPrimeStripEquiv`, not `FPrimeStripEquiv.refl`.
* `S1425SourceGroup I = GraphGroup (upper := S1425RefStrip I)` — the actual
  product of the local Galois groups `Pi v` of the reference strip.
* `S1425GroupEquiv I = MulEquiv.piCongrRight (fun v => (S1425RefLink I).isoPi v)`
  — actual group identification `S1425SourceGroup I ≃* MiddleGraph I`.
* `S1425SourceUnits I v = ((S1425RefStrip I).Mon v)^x` — actual
  F-prime-strip unit groups of the reference strip.
* `S1425UnitsEquiv I v = Units.mapEquiv ((S1425RefLink I).isoMon v)` — actual
  unit identification with `((S01 I).Mon v)^x`, the actual S1388/S1399 carrier.
* `S1425SourceAction I v = ((S1425RefStrip I).unitsAction v).comp
  (Pi.evalMonoidHom _ v)` — the reference strip's actual units action.
* `S1425SourceAction_compat` — the S1399 action-compatibility law, proved from
  the link's `compatAction` via the local units-level equivariance lemma
  `S1425UnitsMapEquiv_unitsAction`.
* **`S1425PaperOxGModuleActual : S1399PaperOxGModule (I := I)
  (G := S1425SourceGroup I)`** — the actual inhabitant of the S1399 first
  field.

## Non-self evidence

* `S1425RefStrip_ne_midStrip : S1425RefStrip I ≠ S1425MidStrip I` — the two
  carriers are distinct actual F-prime-strips (distinct lattice points, aligned
  arithmetic; `primeStrip_ne_of_index_ne_of_arithmetic_eq`).  Hence the group
  and unit identifications are maps between distinct actual carriers, not a
  self-presentation of `S01`.
* `S1425RefLink_eq_actualLink` (rfl): the identification is exactly
  `(I.linkAt 1 0 0 1).primeStripEquiv`.
* No `MulEquiv.refl`/identity Kummer representative is used for the source
  units or the group; the finite-model route is not used.

## First-field projections (all rfl)

`S1425PaperOxGModuleActual_sourceUnits`, `_sourceAction`, `_groupEquiv`,
`_unitsEquiv`, `_units_target` (the units target is literally the S1399 pair
datum's `sourceUnits`), `_action_compat`.

## Axiom check

`#print axioms` on `S1425GroupEquiv`, `S1425UnitsEquiv`, `S1425SourceAction`,
`S1425SourceAction_compat`, `S1425PaperOxGModuleActual`,
`S1425RefStrip_ne_midStrip`, `S1425PaperOxGModuleActual_action_compat` all
report only `[propext, Classical.choice, Quot.sound]`.

## Faithfulness boundary (not claimed)

* The paper's group-theoretic algorithm `G ↦ (G : O^x(G))` (IUT II,
  Example 1.8, (iii)) is still not constructed.
* The identification of the acting group with `Aut(‡A) ≅ G_w` of IUT II,
  Definition 4.9, (ii) is still not constructed.
* What is constructed is the S1399 first field on actual strip data: the paper
  module is realized on a second actual member of the same theater family
  through the actual poly-isomorphism.  The construction does not assert that
  the reference group is the paper's abstract `G`; it only realizes the
  `S1399PaperOxGModule` structure with genuine actual identifications.
* The indiscrete-factor topology (S1388/S1399 convention) is declared only to
  form the type of `S1399ActualPairDatum I` in one rfl-linking theorem; the
  module construction does not depend on it.

## Acceptance status (this package)

* statement_compiles = true (EXIT=0)
* proof_body_checked = true (no sorry/admit; all fields constructed)
* kernel_closed = true for this file (allowed axioms only)
* target_accepted = false (no comparator; S1399 target is a structure, not the
  final xi-f target)
* Not run: Project build, comparator, independent review.

## Next step

The S1399-side consumer can now use `S1425PaperOxGModuleActual`.  The next
substantive step on this line is either (a) re-index the actual S1388 pair datum
`S1399ActualPairDatum` along `S1425GroupEquiv` to obtain a
`KappaOrbitUnitsActionPairDatum` on the reference product group with the same
actual link representatives, or (b) attack the two remaining paper
identifications (group-theoretic algorithm; `Aut(‡A) ≅ G_w`).

EXIT=0
