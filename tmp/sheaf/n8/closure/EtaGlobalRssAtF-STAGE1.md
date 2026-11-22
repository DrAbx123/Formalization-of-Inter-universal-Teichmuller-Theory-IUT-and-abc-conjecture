# Global Rss at the actual F completion

- Task: global region carrier correction.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaGlobalRssAtF.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; zero sorry.

## Carrier

GlobalRegionAtF := Set (K X), where K X is the actual F completion at
nativeFPlaceOverBad.  No base Fmod localFieldAt and no localFieldAt carrier is
used.  Local admissible Rss and global F-level Rss share this carrier, so the
previous carrier bridge is unnecessary.

## Declarations

- GlobalRegionAtF := Set (K X); GlobalAdmissibleAtF := local AdmissibleRegion;
- GlobalRssAtF := local equal-volume quotient;
- globalOpenRegionAtF/globalClosedRegionAtF: actual F open/closed regions;
- globalOpenClassAtF/globalClosedClassAtF: actual F quotient classes;
- localClassToGlobalAtF := identity class map on the shared carrier;
- globalReadoutAtF := local volume readout;
- globalReadoutAtF_eq_local, localClassToGlobalAtF_open: rfl;
- globalOpenClass_ne_globalClosedClass: actual open/closed mass difference;
- local_global_common_carrier_bridge: identity class map, class distinctness,
  and readout equality on the common F carrier.

No arbitrary map, no base Fmod carrier, no carrier bridge.