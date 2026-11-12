# LANA-DECL-CHECKLIST — declarations needed for the full port (A1064)

Status: read-only checklist; no compile.  Batches follow `coord/LANA-PORT-PLAN.md`
and `coord/LANA-PORT-LOG.md`: **L** = LocalConstruct layer (port after Haar/
LocalLogShell/Volume/ScaleVolume), **C** = TG-blocked file but short declaration
to copy into a `Mzk1Ported*` file, **T** = truly TG-dependent (avoid).

| declaration | lana file:line | role | batch | port note |
|---|---|---|---|---|
| `LocalTheory.incl` | `Iut/Concrete/LocalConstruct/Packet.lean:639` | inclusion of a completion factor into the tensor packet | **L** | needs `Factor`, `Tensor`, `completionAt`, `inclFactor` (`:633`); part of LocalConstruct closure |
| `InitialThetaData.scaleEltAt` | `Iut/Concrete/ThetaRegion.lean:126` | `q_{v_l}^{j²}` in the `l`-th tensor factor | **C** | short def; depends `qroot`, `LocalTheory.incl`; copy with minimal context |
| `InitialThetaData.scaleElt` | `Iut/Concrete/ThetaRegion.lean:136` | distinguished-label scale element | **C** | calls `scaleEltAt`; copy together |
| `LocalTheory.factorAut` | `Iut/Concrete/LocalConstruct/IndAut.lean:210` | `ℤ_p`-linear factor automorphisms | **L** | LocalConstruct closure (`IndAut`) |
| `LocalTheory.tensorAut` | `Iut/Concrete/LocalConstruct/IndAut.lean:219` | tensor product of factor automorphisms | **L** | same file |
| `LocalTheory.indAut` | `Iut/Concrete/LocalConstruct/IndAut.lean:299` | full Ind2 automorphism set | **L** | same file |
| `LocalTheory.leastHull` / `Iut.leastHull` | `Iut/WallEquiv/Gap.lean:87` | least `lambda·O` hull | **C** | short def; depends `Tensor`, `integral`, `admissible`; plan says copy |
| `componentVol` | `Iut/Concrete/LocalConstruct/Volume.lean:196` | normalized Haar log-volume | **L** | core LocalConstruct volume; includes `componentVol_mono`, `componentVol_integral` |
| `logShellRadius` | `Iut/WallEquiv/VcI.lean:464` | `sSup(-ordp)` of the local log-shell | **C** | short def; uses `Iut.logShell`/`ordp`; copy with context |
| `ordp_qrootOf` | `Iut/Concrete/ThetaLocalConstruct/Data.lean:328` | `ord_p(q_v)=qOrder/(2ℓe)` | **C/T** | depends ThetaLocalConstruct; copy the statement/proof fragment, not the TG file |
| `rootNormedUnit` | our `tmp/sheaf/xif/paper/PaperRootCompletionTensorActual.lean:120` | `(rootNormedExtension T b)ˣ`, the actual qroot unit | **none** | already in our tree (not lana) |
| `hullOf` | `Iut/Wall/Rss.lean:328` (per plan; `Iut/Wall/Rss.lean`) | hull of a region | **C** | copy minimal def; depends `Region`, `hullAdmissible` |
| `vcIComp` | `Iut/Wall/Ind3.lean:58` | component of `vcI` | **C** | copy with `vcIAt`/`vcI` |
| `vcIAt` | `Iut/Wall/Ind3.lean:80` | admissible region `vcI` at capsule `i` | **C** | copy |
| `vcI` | `Iut/Wall/Ind3.lean:123` | the actual `vcI` region | **C** | copy |
| `vcIPacket` | `Iut/WallEquiv/VcI.lean:683` | `componentVol(vcIComp)` packet | **C** | copy; depends `componentVol` (L) and `vcIComp` (C) |
| `hullPacket` | `Iut/WallEquiv/VcI.lean:689` | `componentVol(leastHull(vcIComp))` | **C** | copy; depends `leastHull`/`componentVol`/`logShellRadius` |

## Batch summary

- **L**: `incl`, `factorAut`, `tensorAut`, `indAut`, `componentVol` (+ Volume/
  ScaleVolume/Haar chain).
- **C copy-only**: `scaleEltAt`, `scaleElt`, `leastHull`, `logShellRadius`, `ordp_qrootOf`,
  `hullOf`, `vcIComp`, `vcIAt`, `vcI`, `vcIPacket`, `hullPacket`.
- **No port**: `rootNormedUnit` (our tree); `RootExtension`/`rootNormedExtension`
  (our tree).
- **T avoid**: TG imports in `Iut/Wall/Checks`, `Iut/Wall/Ind3` etc.; copy-only
  declarations, do not import the files.

## Route B coupling (A1065)

Route B base-changed block needs only:
- `FinitePadicTensor` / `ArithmeticTensorTupleBlock` (LeanFormal green);
- `rootNormedExtension`/`rootNormedUnit` (our tree);
- general unit Haar scaling (`distribHaarChar`, Mathlib/lana `ScaleVolume`, batch L);
- no `leastHull`/`componentVol`/`vcI` unless matching the paper hull region.

## Outstanding

- `LocalTheory.incl` and `componentVol` require the LocalConstruct port batch L
  (Haar/LocalLogShell/Volume/ScaleVolume chain).
- `scaleEltAt`/`leastHull`/`logShellRadius`/`vcI*` are copy-only C; their proofs
  reference TG-blocked Wall context and must be adapted, not imported.
- `ordp_qrootOf` is a local root-order statement; copy the statement and
  `qOrder/(2ℓe)` normalization, do not port `Data.lean`.