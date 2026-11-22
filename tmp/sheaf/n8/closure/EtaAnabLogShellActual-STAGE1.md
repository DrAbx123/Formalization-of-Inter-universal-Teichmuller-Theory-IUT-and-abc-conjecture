# etaAnab actual log-shell data (Rss corrected)

- Task: ETA-2 Rss correction.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaAnabLogShellActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry (Kummer vertical).

## Rss correction

The former `Rss := Real` is replaced by the qside actual log-shell line:

- `abbrev Rss : Type := EtaRssLogShellLineData X`;
- `etaAnabRss : Rss X := etaRssLogShellLineData X` (actual production
  `C2Native.nativeLocalShell` shell, `LogShellVolumeConsumer` index, real
  log-volume coordinate);
- `etaAnabRss_shell_eq` identifies its shell with `localShell.logShell`.

No trivial bare Real line remains.  S/Ind/Kummer data are retained:
- actual `integralStructure := localShell.logShell`; `unitLayer`;
- Ind handling enum and Ind3 upper-semi via
  `VerticalLogKummerCorrespondence.HullDominates`;
- named gap `kummerVerticalActual_obligation`: production has only the
  conditional `VerticalLogKummerCorrespondence` contract, no concrete
  Kummer vertical construction.

No direct Q/hull comparison.