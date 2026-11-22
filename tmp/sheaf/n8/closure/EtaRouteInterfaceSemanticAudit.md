# EtaRouteInterface semantic audit

Audit target: tmp/sheaf/n8/closure/EtaRouteInterface.lean
(SHA F0466B76629884F41389F7755924E73F85A384662516470F0166D02BAEBDCC54)

Scope: audit only. No Lean source was modified.

## Verdict

EtaQ and EtaAnab are NOT the two independent LANA constructions eta^q and
eta^anab_S. They are one and the same p*_v scaling construction and its
algebraic inverse. EtaComparison only proves the inverse laws of that single
scaling plus the native-q sign fact qPilotSignedLog X < 0.

Status: NEGATIVE CONTROL. Do not count EtaRouteInterface as an ETA route
construction and do not feed it into a destination as eta^q/eta^anab_S evidence.

## Evidence

1. Construction site is one equation.

   SourceLogShellDatum.logShell is defined by
     a in logShell <-> (p*_v : K) * a in preLogShell,
   and SourceLogShellCarrier proves
     logShell = invScaledPreLogShell
   by exactly the same multiplication.

   EtaRouteInterface then defines:
     EtaQ a = (p*_v)^{-1} * a
     EtaAnab b = (p*_v) * b.

   Both maps are scalar multiplication by reciprocal constants on the same
   native log-shell datum D = C2Native.nativeLocalShell X. EtaQ's codomain
   proof unfolds logShell = invScaledPreLogShell; EtaAnab's domain proof is the
   defining equivalence of logShell. There is no second construction.

2. EtaComparison is the inverse law of that same scaling.

   EtaComparison X is
     LeftInverse EtaAnab EtaQ / RightInverse EtaAnab EtaQ /
     qPilotSignedLog X < 0.

   The two inverse theorems are proved by
     (p*_v) * ((p*_v)^{-1} * a) = a
     (p*_v)^{-1} * ((p*_v) * b) = b
   using pStar_ne_zero_cast. This is a tautological scaling equivalence, not a
   comparison between independently constructed q-side and anabelian-side
   objects.

3. Native q enters only as a sign.

   EtaNativeQ X := qPilotSignedLog X, and etaNativeQ_neg is
   qPilotSignedLog_neg. No element of the log-shell K is produced from native
   q, no q-pilot/theta image is mapped into Rval or Rss, and no Galois/Kummer
   action is used. The q component of EtaComparison is therefore only q < 0.

## What is still missing for independent eta^q and eta^anab_S

The following exact subitems are required. They are not free maps or free Real
fields; each is an actual source construction or a named gap already identified
in the tree.

### A. q-side eta^q: native q/pilot -> log-shell value

- An actual map from the native q-pilot data to an element of (or a value in)
  the native log-shell K. Current production has no such map:
  SourceLogShellDatum.logMap is Units -> Multiplicative K, not native q -> K;
  qPilotSignedLog is Real and is not mapped to K.
- The source theta-pilot image / source-to-arithmetic value map is also not
  connected to the log-shell: SourceThetaToIQ and the C4/T11 theta carriers
  live on different types.
- Exact missing target: an actual q-side construction
    etaQSource : NativeQData X -> Rval X (or Rss X)
  plus its exact value/commutation theorem. No current declaration supplies it.

### B. anabelian-side eta^anab_S: G_v/Kummer -> Rss

- Native G_v action/descent on the native log-shell family: production has only
  conditional SourceLogShellXMuChainActionCompatibility over a chain supply.
  C2Targets records the exact named gap:
    nativeGvActionTarget_obligation
  and C2Native records that no native C1-indexed action constructed from
  N8NativeInput exists.
- Native Kummer/root-change: production has only
  SourceLogShellDatum.codomainKummerContained : Prop and conditional
  SourceLogShellXMuChainSupply; no actual native root-change map type exists.
  C2Targets records:
    nativeKummerTarget_obligation.
- Archimedean branch: no native archimedean log-shell source object exists in
  the current slice; C2Targets records:
    nativeArchimedeanTarget_obligation.
- Exact missing target: an actual anabelian/G_v/Kummer construction
    etaAnabSource : NativeAnabelianData X -> Rss X (or Rval X)
  using the G_v action and Kummer/root-change, with a separate source
  construction from the q-side.

### C. Nontrivial EtaComparison

EtaComparison must compare the two independently constructed maps, e.g. a
commutative square or equality of the induced log-shell values, not the
inverse laws of one scaling. The exact comparison/commutation theorem is a
separate obligation once A and B exist.

## Minimal correction

- Keep EtaRouteInterface.EtaQ/EtaAnab only as ScaleDown/ScaleUp negative
  controls; do not export them as eta^q/eta^anab_S.
- Do not count etaComparison_actual as an ETA comparison.
- Rebuild EtaQ from the q-side source construction (A) and EtaAnab from the
  G_v/Kummer construction (B); then state EtaComparison as the comparison of
  those two independent constructions.
- Until A and B are supplied, the ETA route remains an exact named gap.

## Evidence index

- tmp/sheaf/n8/closure/EtaRouteInterface.lean: Rval, Rss, EtaQ, EtaAnab,
  EtaComparison, etaQ_leftInverse, etaQ_rightInverse, EtaNativeQ.
- LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean:
  preLogShell, logShell, invScaledPreLogShell,
  logShell_eq_invScaledPreLogShell.
- tmp/sheaf/n8/closure/C2Native.lean:
  nativeLocalShell, NativeLogSlice, exact missing declarations.
- tmp/sheaf/n8/closure/C2Targets.lean:
  nativeGvActionTarget_obligation, nativeKummerTarget_obligation,
  nativeArchimedeanTarget_obligation.

No Lean compiler run is claimed for this audit; facts are definitional reads of
the cited files plus the already compiled EtaRouteInterface.
