# LANA-PORT-TARGETS — C0 minimal target list for `xif_external_port.ps1` (A1002)

Status: hand-porting stopped; script pipeline handoff.  Previously written manual ports
(`Mzk1PortedLocalConstructActual`, `Mzk1PortedLocalVolumeActual`) are kept but no
further manual copies.

## Root targets (pass to -Targets)

1. `Iut/Concrete/LocalConstruct/LocalLogShell.lean`
2. `Iut/Concrete/LocalConstruct/LogShell.lean`
3. `Iut/Concrete/LocalConstruct/Volume.lean`
4. `Iut/Concrete/LocalConstruct/ScaleVolume.lean`

Script should run Analyze first; closure is computed automatically from imports.

## Expected internal closure (from imports)

- `LocalLogShell` -> `PadicLogVolume/PadicLog.lean` (root LANA package; pure Mathlib,
  olean present at `.lake/build/lib/lean/PadicLogVolume/PadicLog.olean`);
- `LogShell` -> `LocalLogShell`, `ThetaAdmissible`, `Arithmetic`;
- `ThetaAdmissible` -> `Admissible`;
- `Arithmetic` -> `Iut/Concrete/ThetaLocalConstruct/Ordp`;
- `Volume` -> `MaximalOrder`, `Archimedean`, `Haar`;
- `MaximalOrder` -> `Indeterminacy`;
- `Archimedean` -> `MaximalOrder`;
- `ScaleVolume` -> `TensorIntegral`;
- `TensorIntegral` -> `Volume`, `Arithmetic`.

So the real closure is roughly the LocalConstruct core:
`Haar`, `LocalLogShell`, `Admissible`, `ThetaAdmissible`, `Arithmetic`, `Ordp`,
`MaximalOrder`, `Indeterminacy`, `Archimedean`, `LogShell`, `Volume`,
`TensorIntegral`, `ScaleVolume`, plus `PadicLogVolume/PadicLog`.
The script's Analyze output should be treated as authoritative.

## Why manual porting stopped

Our manual attempts only reached `Haar` and `LocalLogShell` because the remaining
files need the multi-file LocalConstruct internal chain, whose lana oleans are absent
from the root build.  This is **not a TG dependency**:
- `TemperedFundamentalGroups/*` is above the LocalConstruct/Concrete layer and is
  not imported by these files;
- the blockers are missing internal lana oleans (`Arithmetic` -> `Ordp`,
  `ThetaAdmissible` -> `Admissible`, `Volume` -> `MaximalOrder`/`Archimedean`,
  `ScaleVolume` -> `TensorIntegral`), which the script ports as a closure.

## TG audit of targets

None of the four root targets imports `TemperedFundamentalGroups`; the import
graph above stays inside `Iut/Concrete/LocalConstruct` and
`Iut/Concrete/ThetaLocalConstruct/Ordp`.  TG enters only in Wall/Concrete layers
above, which are not in this C0 target list.

## Not in this batch

- `Iut/WallEquiv/VcI.lean` (`logShellRadius`, `hullPacket`): imports
  `Iut.WallEquiv.Gap`, hence the Wall chain (TG-adjacent and large).  Separate
  target after C0; do not mix into the C0 port.

## Suggested commands (mainline)

```powershell
pwsh tools/xif_external_port.ps1 -Name lana_c0 -SrcRoot D:\lean \
  -Targets 'Iut/Concrete/LocalConstruct/LocalLogShell.lean;Iut/Concrete/LocalConstruct/LogShell.lean;Iut/Concrete/LocalConstruct/Volume.lean;Iut/Concrete/LocalConstruct/ScaleVolume.lean' \
  -Analyze
# inspect import_chain.md, then:
pwsh tools/xif_external_port.ps1 -Name lana_c0 -SrcRoot D:\lean -Targets '...same...' -Port
# output expected: tmp/external/ported/lana_c0/...; hand to watchdog for Compile.
```

## Deliverables to mainline

- this target list;
- the dependency map above;
- note that `tmp/external/ported/lana_c0` is the port root output; watchdog should
  compile it dependency-ordered (script has -Compile option if mainline prefers).
