# LANA-B minimal layered port plan (A1043, mainline; for stepxi review)

Goal: pin down the ind2 reading (`ind2Term`, `archDefect`, `gapHullAt`) with the
smallest possible ported closure, reusing the already-green lana_a base.

## Decl coordinates (lana root tree)
| decl | file:line | direct deps (names) |
|---|---|---|
| `leastHull` | Iut/WallEquiv/Gap.lean:87 | `RationalPlace`, `Place K`, `Tensor K vQ c`, `integral K vQ c`, `IsUnit`, `•` |
| `archDefect` | Iut/WallEquiv/Gap.lean:459 | `componentVol`, `leastHull`, `logShell`, `componentVol_le_leastHull_self`, `LocalConstruct.archLogShell_admissible` |
| `ind2Term` | Iut/WallEquiv/Gap.lean:747 | `InitialThetaData.Lab`, `LocalTheory.{Fiber,componentVol,tuple,leastHull,shell,shell_admissible}`, `nC`, `D.thetaComponent/placeSect/Kt/Fmod/scaleElt`, `Nat.Primes` |
| `ind2Term_nonneg` | Gap.lean:756 | as ind2Term + `isUnit_scaleElt`, `shell_admissible` |
| `gapHullAt` | Gap.lean:895 | ind2Term + `tupleWeight`, `RationalPlace` |
| `orderVol` | Iut/WallEquiv/VcI.lean:93 | `componentVol` family |
| `logShellRadius` | Iut/WallEquiv/VcI.lean:464 | `logShell`, `Ordp`-style radius input (see hull note) |
| `defectPacket` | Iut/WallEquiv/VcI.lean:703 | archDefect/ind2Term + `hullPacket` inputs |
| `componentVol_units_smul` | Iut/Wall/IdentifiedCopies.lean:67 | `componentVol`, units action |
| `logVol_hull_vcI_eq` | Iut/WallEquiv/VcI.lean:741 | hull + componentVol layers |

## Layer 0 - GREEN BASE (already compiled, oleans fresh)
lana_a ported tree (7/7 DONE): `tmp/external/ported/lana_a/Iut/Cor312/`
- Procession, RationalPlace, PacketPresentation, Container, HolomorphicHull, ContainerHull, LogVolume
(external DrAbx123/lean @ 9399e9fab; same lean v4.32.2 / mathlib 905b95818e; no TG inside this closure).

## Layer 1 - copy-only decl extractions (DRAFTS, not green)
Hull produced copy-only drafts (source text extracted, lana context NOT adapted):
- `tmp/sheaf/xif/paper/Mzk1PortedGapDefsActual.lean`: archDefect (Gap:459), ind2Term (:747), ind2Term_nonneg (:756), gapHullAt (:895)
- `tmp/sheaf/xif/paper/Mzk1PortedVcIDefsActual.lean`: orderVol (:93), shellExcess (:158), logShellRadius (:464), defectPacket (:703), logVol_hull_vcI_eq (:741), hullPacket_finite (:806), hullPacket_tame (:844)
- `tmp/sheaf/xif/paper/Mzk1PortedIdentifiedCopiesDefsActual.lean`: componentVol_units_smul (IdentifiedCopies:67)
Status: NOT compilable as-is (references lana context: componentVol/leastHull/Tensor/InitialThetaData).

## Layer 2 - LocalConstruct minimal closures (non-TG in principle; depends on internal chain)
Root targets for a scripted port:
- Iut/Concrete/LocalConstruct/{LocalLogShell, LogShell, Volume, ScaleVolume}.lean (hull A1002 targets)
- Iut/Concrete/LocalConstruct/{Archimedean, ArchLogShell, Haar, LatticeSandwich, MaximalOrder, Indeterminacy, Theory, Prop14}.lean
- PadicLogVolume/{PadicLog, TraceDuality}.lean (root `PadicLogVolume` tree, oleans already present)
Already green in LocalConstruct: Haar, LocalLogShell, LogLattice (oleans). Everything else missing olean.
Closure sizes measured with tools/closure_analyze.mjs: (target closure / missing / TG count)
- LocalConstruct/IndAut: 1158 / 96 / TG 744
- Concrete/ThetaRegion: 1179 / 112 / TG 744
- WallEquiv/Gap: 1732 / 287 / TG 744 + Pi1 65
- Tripod/Providers: 1216 / 139 / TG 744
=> TG enters through the upper layers (InitialThetaData/Existence/Tripod), NOT through LocalConstruct
   primitives themselves; but every WallEquiv/Concrete target closure already imports the TG root chain.

## Layer 3 - InitialThetaData / LocalTheory (THE TG-adjacent bottleneck)
ind2Term needs `D : InitialThetaData` and `LocalTheory.*` only at the level of
- `InitialThetaData.Lab`, `.Fmod`, `.Kt`, `.placeSect`, `.thetaComponent`, `.scaleElt`
- `LocalTheory.{Fiber, componentVol, tuple, leastHull, shell, shell_admissible}`
These come from `Iut/Concrete/Existence.lean` + `Iut/Concrete/LocalTheory.lean` + `Iut/Tripod/*`.
Options to review with stepxi:
(a) extract ONLY the structure/def layer of InitialThetaData+LocalTheory (declaration closure, no theorems)
    and port it (TG deps may be only for the *theorems*, not for the field types);
(b) define the ind2 layer as an interface over an abstract `D` (fields given as hypotheses),
    which is what our paper files already do (`Mzk1Ind2Term*` style);
(c) full Layer 3 port = multi-thousand-line TG closure - NOT recommended in this round.

## Layer 4 - WallEquiv hull/vcI (after Layer 2/3)
`hullOf`, `vcI`, `vcIComp`, `tupleWeight`, `hullPacket*` from Iut/Wall/* and Iut/WallEquiv/*;
needs Layer 3 for `InitialThetaData`-indexed definitions.

## Recommended minimal deliverable for stepxi
1. Port Layer 2 LocalConstruct targets (script; watch TG count in closure - reported above).
2. Extract Layer 3 declaration-only closure for InitialThetaData/LocalTheory via
   `xif_external_port.ps1 -Analyze` (or our closure_analyze.mjs if script hangs) and check
   whether TG files are *proof* deps only; if so, port declarations with `-Port` and stub-free adapt.
3. Adapt Layer 1 drafts against Layer 2+3 names; compile via watchdog only.
4. Defer Layer 4 to after 1-3 are green.

## Evidence / tooling
- lana_a Analyze: targets=7, closure=7, missing=0, TG=0 (script xif_external_port.ps1).
- Port fixes applied to script: UTF8-no-BOM writes; UTF8 reads (mojibake fix).
- Read-only closure analyzer: tools/closure_analyze.mjs (fast; used when script -Analyze hung >30min).
