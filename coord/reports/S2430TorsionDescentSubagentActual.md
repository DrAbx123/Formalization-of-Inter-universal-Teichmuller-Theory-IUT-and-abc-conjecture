# S2430: torsion descent — S2179TransferCompatible closed

Node: S2430 (torsion descent from S2371 to S2179).
Layer: O (S2179 stage compatibility).
Source object: `S2179TransferCompatible` (S2179StageConjEquivActual), i.e.
`S2422StageDescentRequired` (S2422StageDescent3Actual).
Consumer: `S2422StageDescentRequired` / `S2300StageCompatibleRequired` /
`S2343StageCompatibleRequired` / `S2338StageCompatibleRequired` (all the same
Prop as an abbrev).

## Result

**Closed.** `S2430_transferCompatible : S2179TransferCompatible (p := p)` is
proved, and consequently `S2430_stageDescentRequired :
S2422StageDescentRequired (p := p)`.  No sorry, no new axiom, no fabricated
object; the axiom probes list exactly the allowed set
`propext, Classical.choice, Quot.sound`.

Exact first missing: **none for this surface**.  (The wider S2169 target
`S2169MuQZActionData`, whose fields `muQZAction` / `action_compat` are not
produced here, is unchanged by this file.)

## Method

Three ingredients, all actual:

1. `S2430_cast_equiv_eq_trans` : for subgroups `A B X <= G` and `h : A = B`,
   `(h ▸ e : ↥X ≃* ↥B) = e.trans (MulEquiv.subgroupCongr h)` (by `cases h`, then
   `ext`/`rfl`).  This is the "coefficient formula" that removes the
   `h ▸ e` transport in `S2179StageConj`.
2. `S2430_stageConj_eq` / `S2430_stageConj_apply` : the underlying
   abelianization coefficient of `S2179StageConj p g H` is
   `abelianizationCongr (S2200ConjEquiv p g H)`, i.e. on a torsion element the
   map is `Abelianization.map (S2200ConjEquiv p g H).toMonoidHom`.  Both
   `S2179StageConj` and `S2200ConjEquiv` are built from the *same*
   `Subgroup.equivMapOfInjective H.toSubgroup (MulAut.conj g.symm).toMonoidHom`;
   they differ only by transport along `S2179MapConjEqComap` versus composing
   with `MulEquiv.subgroupCongr` of it, which (1) identifies.
3. `S2371_verlagerung_natural` (= `S2300VerlagerungNaturalRequired`, proved in
   S2371HnatExplicitActual from `S2371_hnat`, `S2343_transferAb_natural_hom`,
   `S2348_transferAb_subgroupCongr`, `S2341_abmap_inclusion`) instantiated at
   the *underlying abelianization element* of an arbitrary `v : Stage p K`.

Pointwise assembly in `S2430_transferCompatible`:

* write `v = Additive.ofMul w` with `w : CommGroup.torsion (Abelianization ↥K)`;
* `S2430_toStage_apply` : `toStage p h (Additive.ofMul w) =
  Additive.ofMul (torsionMap (verlagerungOpen p h) w)` (rfl);
* `S2430_stageConj_apply` on the outer and inner `S2179StageConj`;
* `Additive.ext` + `Subtype.ext` + the coercion lemmas
  `S2430_torsionCongr_coe` / `S2430_torsionMap_coe` (both rfl) reduce the
  `Stage` equality to the abelianization equation
  `Abelianization.map eH (verlagerungOpen p h w) =
   verlagerungOpen p h' (Abelianization.map eK w)`,
  which is `DFunLike.congr_fun hnat w` for the same witness `h'` produced by
  `S2371_verlagerung_natural`.

Note: no case analysis on the transported equivalence is made (the single
`cases h` is in the general subgroup cast lemma `S2430_cast_equiv_eq_trans`,
which is then applied once).

## Declarations added (all proved)

| name | statement |
|---|---|
| `S2430_cast_equiv_eq_trans` | `h ▸ e = e.trans (MulEquiv.subgroupCongr h)` for `e : ↥X ≃* ↥A`, `h : A = B` |
| `S2430_torsionCongr_coe` | `↑((torsionCongr e) w) = e ↑w` |
| `S2430_torsionMap_coe` | `↑((torsionMap f) w) = f ↑w` |
| `S2430_toStage_apply` | `toStage p h (Additive.ofMul w) = Additive.ofMul ((torsionMap (verlagerungOpen p h)) w)` |
| `S2430_stageConj_eq` | `S2179StageConj p g H = (torsionCongr (abelianizationCongr (S2200ConjEquiv p g H))).toAdditive` |
| `S2430_stageConj_apply` | pointwise form of the above on `Additive.ofMul w` |
| `S2430_transferCompatible` | `S2179TransferCompatible (p := p)` |
| `S2430_stageDescentRequired` | `S2422StageDescentRequired (p := p)` |

## Build

Standard compile, from `D:\lean`:

`lake env lean -j1 -R D:\lean -o D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2430TorsionDescentSubagentActual.olean tmp/sheaf/xif/paper/S2430TorsionDescentSubagentActual.lean`

* EXIT = 0
* Lean: 4.32.2, Mathlib (project pin)
* Source: `tmp/sheaf/xif/paper/S2430TorsionDescentSubagentActual.lean`
  * SHA256 `E9BB85FFB7ED00369423338F9A750105E40CF5DF5319AA8DEC831C5EE2B8F691`
* Olean: `D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2430TorsionDescentSubagentActual.olean`
  * SHA256 `E62865A5EFE58B4121DB8EE82BA6A571CF95C1AF94105F4284ACE0FD75A3615C`
* Log: `tmp/sheaf/xif/paper/S2430TorsionDescentSubagentActual.out`

## Axioms (`#print axioms`, from the compile log)

All eight declarations: `[propext, Classical.choice, Quot.sound]` only.
In particular `S2430_transferCompatible` and `S2430_stageDescentRequired`
carry no `sorryAx`.

## Status flags

* statement_compiles: yes (`#check` confirms the exact types
  `S2179TransferCompatible p` / `S2422StageDescentRequired p`).
* proof_body_checked: yes (olean produced, EXIT = 0).
* kernel_closed: yes (axiom probe as above).
* target_accepted: not run (no comparator / independent review; full Project
  build not run).

## Dependencies (all pre-existing, none modified)

`tmp/sheaf/xif/paper/S2422StageDescent3Actual.lean`,
`tmp/sheaf/xif/paper/S2371HnatExplicitActual.lean` (transitively S2343, S2338,
S2341, S2348, S2317, S2200, S2179, S2173, S2169, S2017).  No other file was
edited; `tmp/xif_compile_queue.txt` was not touched.
