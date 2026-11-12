# PORTED-DECL-STATUS — lana_tgfree ported declarations (A1091)

Status: read-only audit of `tmp/external/ported/lana_tgfree` and
`.lake/build/lib/lean/tmp/external/ported/lana_tgfree`; no compile.

## 0. Port layout

- Source root: `tmp/external/ported/lana_tgfree/`;
- OLean root: `.lake/build/lib/lean/tmp/external/ported/lana_tgfree/`;
- Import prefix: `tmp.external.ported.lana_tgfree.Iut....`;
- **Namespace stays `Iut`** (source content unchanged); e.g.
  `Iut.LocalConstruct.componentVol`, `Iut.WallEquiv.leastHull`,
  `Iut.InitialThetaData.scaleElt`.
- Ported oleans currently: **38 files** (out of ~300 source files).
  Green examples: `Iut/Concrete/LocalConstruct/Haar.olean`,
  `.../LocalLogShell.olean`, `Iut/AutHolomorphic/*`, `Iut/EtaleTheta/*`
  (partial), `Iut/Wall/BPS.olean`.

## 1. Requested declarations

| declaration | ported source | olean? | status |
|---|---|---|---|
| `Iut.InitialThetaData.scaleElt` / `scaleEltAt` | `Iut/Concrete/ThetaRegion.lean:126/136` | **no** | source only; upstream `ThetaLocalConstruct.Data`/`Cor312.Statement` not compiled |
| `Iut.LocalConstruct.incl` | `Iut/Concrete/LocalConstruct/Packet.lean:639` | **no** | source only; Packet/Volume dependencies not compiled |
| `Iut.WallEquiv.leastHull` | `Iut/WallEquiv/Gap.lean:87` | **no** | source only; Gap/Forms/TG-adjacent deps not compiled |
| `Iut.LocalConstruct.componentVol` | `Iut/Concrete/LocalConstruct/Volume.lean:196` | **no** | source only; MaximalOrder/Archimedean/Volume deps not compiled |
| `Iut.WallEquiv.logShellRadius` | `Iut/WallEquiv/VcI.lean:464` | **no** | source only; VcI/WallEquiv deps not compiled |
| `Iut.InitialThetaData.qrootOf` / `ordp_qrootOf` | `Iut/Concrete/ThetaLocalConstruct/Data.lean:328` (and qroot defs earlier) | **no** | source only; ThetaLocalConstruct closure not compiled |
| `Iut.InitialThetaData.thetaComponent` / `ivLabels` / `litLabels` | `Iut/Concrete/ThetaRegion.lean:236/241/257` | **no** | source only; same closure as scaleElt |

**Ported/green related:**
- `Iut/Concrete/LocalConstruct/Haar.lean` — olean **yes**;
- `Iut/Concrete/LocalConstruct/LocalLogShell.lean` — olean **yes**;
- `Iut/Concrete/LocalConstruct/LogShell.lean` — olean **no**
  (needs LocalLogShell + ThetaAdmissible + Arithmetic);
- `Iut/Wall/BPS.lean` — olean **yes** (unrelated to the list).

## 2. Why the key files are not compiled

The ported import graph is file-for-file; the key declarations sit above
uncompiled internal files:
- `ThetaRegion` -> `ThetaLocalConstruct.Data` -> `Ordp`/`Roots`/`TateCompat`;
- `Gap` -> `WallEquiv.Forms` -> more Wall/Concrete files;
- `VcI` -> `Gap`;
- `Volume` -> `MaximalOrder` -> `Indeterminacy`; `Archimedean` ->
  `MaximalOrder`; `Haar` green;
- `Packet` -> `LocalLogShell`/`Theory`/`FactorShell`;
- `IdentifiedCopies` -> `Wall.Checks` (TG-adjacent).

Only Haar and LocalLogShell are currently green in the requested neighbourhood.

## 3. Minimal import checklist for Form C / structural object

### 3.1 Current Form C file (no ported lana needed)
`tmp/sheaf/xif/paper/Mzk1StructuralLineBundleActual.lean` imports:
- `tmp.sheaf.xif.paper.DeterminantLogVolumeActual` (green);
- `tmp.sheaf.xif.paper.S2735QPilotLineBundleActual` (green);
- `tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol` (green);
- `Mathlib.Tactic`.
No `tmp.external.ported...` import is needed for the arithmetic conclusion.

### 3.2 Structural object needing actual theta/volume fields
To replace the GAP Props by actual theta/q data, import (once compiled):

| needed declaration | import module | namespace |
|---|---|---|
| `componentVol`, `componentVol_integral` | `tmp.external.ported.lana_tgfree.Iut.Concrete.LocalConstruct.Volume` | `Iut.LocalConstruct` |
| `incl` | `...Iut.Concrete.LocalConstruct.Packet` | `Iut.LocalConstruct` |
| `scaleElt`, `scaleEltAt`, `thetaComponent`, `ivLabels`, `litLabels` | `...Iut.Concrete.ThetaRegion` | `Iut.InitialThetaData` |
| `ordp_qrootOf`, `qrootOf` | `...Iut.Concrete.ThetaLocalConstruct.Data` | `Iut.InitialThetaData` |
| `leastHull`, `gapTerm`, `ind2Term`, `gapHullAt` | `...Iut.WallEquiv.Gap` | `Iut.WallEquiv` |
| `logShellRadius`, `vcIPacket`, `hullPacket` | `...Iut.WallEquiv.VcI` | `Iut.LocalConstruct`/`Iut.WallEquiv` |
| `componentVol_units_smul` | `...Iut.Wall.IdentifiedCopies` | `Iut.Wall` (copy; TG-adjacent) |
| `logVol`, `processionVol` | `...Iut.Cor312.LogVolume` | `Iut.LogVolumeData` |
| `indAut`, `factorAut`, `tensorAut` | `...Iut.Concrete.LocalConstruct.IndAut` | `Iut.LocalConstruct` |

### 3.3 Build order (minimal)
1. `Haar` (green), `LocalLogShell` (green);
2. `Admissible`/`Arithmetic`/`ThetaAdmissible`;
3. `LocalConstruct.Volume`/`ScaleVolume`/`Packet`/`IndAut`;
4. `ThetaLocalConstruct.Data`;
5. `Cor312.Statement`/`LogVolume`;
6. `ThetaRegion`;
7. `WallEquiv.Forms`/`Gap`/`VcI`.

## 4. Status summary

| item | green? |
|---|---|
| Haar | yes |
| LocalLogShell | yes |
| LogShell | no |
| componentVol | no |
| incl | no |
| leastHull | no |
| logShellRadius | no |
| qrootOf/ordp_qrootOf | no |
| scaleElt/scaleEltAt | no |
| thetaComponent/ivLabels/litLabels | no |

Form C arithmetic is independent of these; the structural actual object is
blocked until the LocalConstruct/ThetaRegion/WallEquiv closure is compiled.
