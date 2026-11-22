# Actual global qO class in GlobalRssAtF

- Task: bypass FLevelGlobalClassBridge and define qO class/readout directly in
  canonical GlobalRssAtF.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/EtaQOClassGlobalActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0; one named sorry.

## Actual construction

- globalQOCarrier := closedBall 0 ||nativeQ.q|| at the actual F completion
  (the qORegion closed-ball form);
- globalQOAdmissible: actual positive finite admissible region;
- globalQOClass := rssOf globalQOAdmissible in GlobalRssAtF;
- globalQOReadout := log of its volume readout;
- globalQOReadout_eq: rfl, equals log muK(globalQOCarrier).

## Readout relation

- Conditional actual theorem: if muK(globalQOCarrier) = muQ(qORegion), then
  globalQOReadout = qOClassReadout.  Proved by qOClassReadout_eq.
- Exact gap: QOReadoutRelationTarget states the unconditional equality; named
  sorry.  The missing input is the actual measure agreement between the
  canonical GlobalRssAtF measure and the multiradial QCompletion Haar measure
  on the qO region.  No arbitrary quotient map is used.