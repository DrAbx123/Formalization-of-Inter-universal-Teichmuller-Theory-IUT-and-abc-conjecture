# C2 Kummer / root-change - stage 1 no-go

- Node: C2 child (Kummer/root-change).
- Owner: logdescent.
- Status: exact no-go; no local structure added.

Required: an actual Kummer/root-change map on the C1-indexed source finite
places, compatible with the local log-shell and principal units.

Actual production data: `SourceLogShellDatum.codomainKummerContained`
(IUTII/Kummer/SourceLogShellCarrier.lean:134) is only the Prop
`unitLayer subset logShell`; `kummerImages_mem_logShell` proves the containment
for available images but does not construct a Kummer/root-change map.
`SourceLogShellXMuPacket`/`SourceLogShellXMuChainSupply` are conditional chain
supplies over datum families, not the source Kummer arrow.

Exact missing interface: a C1-indexed Kummer/root-change map type and its
construction/compatibility with the actual principal units and log-shell.
No such type exists in C2/C1.  Not assumed, not added.