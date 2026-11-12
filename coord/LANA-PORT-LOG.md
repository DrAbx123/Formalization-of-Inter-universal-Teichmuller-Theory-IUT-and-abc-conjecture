# LANA-PORT-LOG — hull port progress

Status: first port written (not compiled; handed to watchdog).  Date 2026-11-12.

## Ported

| our file | source (lana root tree) | contents | TG dependencies |
|---|---|---|---|
| `tmp/sheaf/xif/paper/Mzk1PortedLocalConstructActual.lean` | `Iut/Concrete/LocalConstruct/Haar.lean` | Haar modulus of `p` on `ℚ_p`/finite-dim vector spaces: `measure_preimage_mul_padic`, `measure_preimage_smul_padic`, coset/ball decompositions | None (`import Mathlib` only) |

Adaptation notes:
- copyright/attribution header retained (Apache-2.0, LANA Project);
- namespace changed to `LeanFormal.IUT.XiFPaper.Mzk1PortedLocalConstructActual`;
- imports reduced to `Mathlib` (source also imports only `Mathlib`);
- all declarations/lemmas copied verbatim otherwise.

## Not ported yet

- `LogShell.lean`: depends on `LocalLogShell`, `ThetaAdmissible`, `Arithmetic`,
  and number-field completion/Tensor/Factor carriers; not TG, but a multi-file
  LocalConstruct closure.  Next after Haar.
- `Volume.lean`: depends on `MaximalOrder`, `Archimedean`, `Haar`, and the
  `Tensor`/`haar` construction; needs the LogShell/Arithmetic chain.
- `ScaleVolume.lean`: depends on `TensorIntegral`, `LocalTheory` volume API;
  after LogShell/Volume.
- No TG-dependent file encountered in this batch; the TG dependency issue is
  in the Wall/Concrete layer above (A866/A877 findings), not in Haar.

## Compilation

Not run manually (project discipline).  File handed to mainline/watchdog;
expected to compile with Mathlib only, but the `PadicInt`/`Padic` API is
version-sensitive — watchdog will report first error if any.

## Second batch (A1001)

| our file | source | contents | dependency status |
|---|---|---|---|
| `tmp/sheaf/xif/paper/Mzk1PortedLocalVolumeActual.lean` | `Iut/Concrete/LocalConstruct/LocalLogShell.lean` | `logShell`, `mem_logShell`, `logShell_isBounded`, `isCompact_closure_logShell`, `logShell_subset_closedBall`, `closedBall_subset_logShell`, `integer_subset_logShell`, `logShell_eq_closedBall`, `logShell_eq_integer` | `PadicLogVolume.PadicLog` (root LANA package, olean present); no TG |

Adaptation: namespace `LeanFormal.IUT.XiFPaper.Mzk1PortedLocalVolumeActual`; source comments retained; imports reduced to `PadicLogVolume.PadicLog`.

### Skipped/blocked in this batch

- `LogShell.lean` (tensor log-shell): imports `LocalLogShell`, `ThetaAdmissible`,
  `Arithmetic`; needs the LocalConstruct internal chain (`Arithmetic` ->
  `Iut/Concrete/ThetaLocalConstruct/Ordp`, `ThetaAdmissible` -> `Admissible`).
  Not TG, but the lana internal oleans are absent; skip until stepxi's closure plan.
- `Volume.lean`: imports `MaximalOrder`, `Archimedean`, `Haar`; constructs
  `integralAt`, `haar`, `componentVol`; requires the full LocalConstruct chain
  (Tensor/Factor/LocalTheory).  Skip for now; Haar alone is ported.
- `ScaleVolume.lean`: imports `TensorIntegral` (which imports `Volume` and
  `Arithmetic`); needs the Volume chain.  Skip.
- `logShellRadius` (WallEquiv/VcI.lean:464) depends on `ordp` from
  `Iut/Concrete/ThetaLocalConstruct/Ordp`; not portable until that module is in
  the tree.  Recorded as a dependency for the next batch.

No TG-dependent file was encountered in the two ported files; TG appears in
Wall/Concrete layers above.
