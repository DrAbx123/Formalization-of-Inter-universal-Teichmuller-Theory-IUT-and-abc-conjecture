# S1977: levelwise realification functional of the actual p-adic log-shell

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1977LevelwiseRealificationActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1977LevelwiseRealificationActual.olean
Consumer: tmp/sheaf/xif/paper/_S1977Consumer.lean
Upstream: tmp/sheaf/xif/paper/S1961LocalGlobalBridgeActual.lean (sole import)

## Verification

- Plain check:
  lake env lean tmp/sheaf/xif/paper/S1977LevelwiseRealificationActual.lean
  EXIT=0, 0 errors, 0 warnings (log logs/S1977_compile1.log).
- Olean build:
  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1977LevelwiseRealificationActual.olean tmp/sheaf/xif/paper/S1977LevelwiseRealificationActual.lean
  EXIT=0, log logs/S1977_olean.log (54 lines, only the #print axioms output).
- Source: 605 lines, 28443 bytes,
  SHA256 20E5BDE82228449B755E71A857ABBF79836D2CC8AD6307CA8F75B04B39BA8C20.
- Olean: 680032 bytes,
  SHA256 E047138549BA45DA1EAC68E13F43507B06B15AAA7534BA11F17AA2ED0E0644CA.
- Axiom audit (#print axioms on 18 main declarations): every one is
  [propext, Classical.choice, Quot.sound]; no sorryAx, no axiom declaration.
- Forbidden-token scan: the only occurrences of sorry / admit / axiom are the
  honesty paragraph and the #print axioms probes; there is no sorry or admit
  tactic and no axiom declaration.
- Imports: only S1961LocalGlobalBridgeActual (hence S1949, S1958, S1927 and the
  actual completion/norm-log transport); no new import.
- Consumer: _S1977Consumer.lean compiles against the *built olean*
  (EXIT=0, logs/S1977_consumer.log) with #check's of the whole interface and
  uses of the main theorems; its olean is 3840 bytes,
  SHA256 B11C7F75B61EE4539EEEFE019644C357B84FFFC11FF0545C7084A1ECF45088DD
  (source SHA256 0D7E66BE10BE338DF4AD54D41621D2DE8C1DFB685D26B4CFC08B6F590D14F75B).

Status of the four separate reports:
- statement_compiles = true (type-correct statements, no metavariables).
- proof_body_checked = true (the file elaborates by lake env lean, EXIT=0).
- kernel_closed = true (axiom probes; no sorryAx).
- target_accepted = not claimed: this is a tmp package, no locked target, no
  Lean comparator run. Project automation (tools/lean_auto.py) was not used.

## The question

S1961 proved the IQ (Q-span) bridge

  bridgeFiber v = Submodule.span Q (realBridge v '' actualLogShell_v),
  bridgePacket = paperGlobalLogShellPacket,
  P.finiteLogShell = bridgePacket   for every P : S1927FullLogKummerUQ D.

It explicitly does *not* prove the levelwise equality
  realBridge v '' actualLogShell_v = (paperLogShellDatum v).logShell,
and it names the remaining object: "an additive real-valued functional on
Completion (QPlace v) compatible with the norm-log readout".

## Main finding: that object does not exist (theorem, not a missing lemma)

no_additive_realification (v : FinitePrimePlace 2 7) :

  not exists L : Completion (QPlace v) ->+ R,
    forall x in (actualLocalLogShellDatum v).logShell, L x = realBridge v x.

Proof (all objects are the actual S1949/S1927 ones):
- Let pi := actualUniformizer v, so log ‖pi‖ != 0 (actualUniformizer_logNorm_ne_zero)
  and pi is in the actual log-shell (O_v is contained in it, S1949).
- The actual log-shell is an AddSubgroup, so a := pi, a2 := a + a and
  a4 := a2 + a2 all lie in it (SourceLogShellDatum.add_mem_logShell).
- Additivity plus agreement on the shell at a and a2 forces
  log ‖a + a‖ = 2 log ‖a‖; multiplicativity of the norm gives
  ‖a + a‖ = ‖2‖ ‖a‖, hence log ‖2‖ = log ‖a‖.
- The same at a2 gives log ‖2‖ = log ‖a + a‖ = log ‖2‖ + log ‖a‖, hence
  log ‖a‖ = 0, contradicting log ‖pi‖ != 0 (pi < 1).

So the obstruction is a *contradiction in the compatibility data*, not a
missing lemma: the shell contains an additive subgroup on which the
multiplicative norm-log readout is not additive.

Consequences formalized:

- LevelwiseRealificationFunctional v (additive Completion ->+ R, agreeing with
  the bridge on the shell, image = reduced shell) is an empty type:
  levelwiseRealificationFunctional_not_nonempty.
- The levelwise set equality is false *even without additivity*:
  levelwise_equality_false : realBridgeImage v != paperLogShell v,
  levelwise_equality_false_datum : realBridgeImage v != (paperLogShellDatum v).logShell.
  Proof: the bridge image is bounded above (the shell is compact hence bounded,
  completionLogShell_norm_bound / actualLogShell_norm_bound /
  realBridgeImage_boundedAbove) while the reduced shell is unbounded above
  (paperLogShell_unbounded: the p*-inverse-scaled multiples of the positive
  norm-log of pi^{-1}).
- Consequently no function whatsoever, additive or not, is both the norm-log
  readout on the actual shell and levelwise onto the reduced shell:
  no_levelwise_realification_function.

## What is constructed instead (the honest levelwise realification)

The real-valued functional compatible with the norm-log readout exists on the
*multiplicative* group of the completion, written additively:

  additiveNormLog v : Additive ((Completion (QPlace v))^x) ->+ R,
    u |-> Real.log ‖u‖,
  levelwiseNormLog v : (Completion (QPlace v))^x -* Multiplicative R,

with additiveNormLog_ofMul / levelwiseNormLog_apply: on every unit it reads out
exactly the S1961 bridge realBridge v u = log ‖u‖.

It identifies the reduced S1927 datum *levelwise* (set identities, not spans):

  paperPreLogShell v = range (u |-> levelwiseNormLog v u).toAdd
    (paperPreLogShell_eq_levelwiseNormLog_range),
  paperLogShell v = (fun a => (p*_v)^{-1} * a) '' range (u |-> levelwiseNormLog v u).toAdd
    (paperLogShell_eq_levelwiseNormLog_image).

where paperPreLogShell / paperLogShell are the S1927 reduced sets with the real
codomain made explicit (definitions 0 of the file).

## Why the actual datum cannot be realified levelwise

The actual datum's Units are the integral units O_v^x, the reduced datum's Units
are the full multiplicative group K_v^x.  For integral units the norm-log
readout is trivial:

  completionUnits_norm_eq_one : ‖(u : O_v) : K_v‖ = 1,
  realBridge_image_completionUnits : realBridge v '' (range of O_v^x) = {0}.

So the levelwise norm-log image of the actual unit group is {0}, while the
reduced shell is the nonzero p*-scaled lattice generated by log ‖u‖ (u in K_v^x).
Any functional that agrees with the norm-log readout on the actual units
therefore kills the pre-log-shell (additive_functional_trivial_on_preLogShell),
and cannot reach the reduced shell.  Conversely, an additive functional that
agrees with the bridge on the *elements* of the shell is inconsistent (above).

## Exact first missing (precise replacement of the proposed functional)

The remaining object is not a functional on the additive group of
Completion (QPlace v).  The missing datum is an identification

  O_v^x  ~  K_v^x

of the actual integral unit group with the completion's full multiplicative
group, *compatible with the norm-log readout* (a uniformizer splitting under
which the identically zero norm-log of integral units is compared with the
lattice Z * log ‖pi‖ of field units).  Such an identification cannot be
norm-log compatible, because the left readout is trivial
(realBridge_image_completionUnits).  What survives, and is sharp, is the Q-span
comparison of S1961:

  s1977_span_bridge_sharp : Submodule.span Q (realBridgeImage v)
    = Submodule.span Q ((paperLogShellDatum v).logShell : Set R).

Hence: the levelwise bridge is impossible; the correct realification is the
multiplicative one constructed here, and the paper-level comparison has to be
read at the Q-span / log-volume level.  No fake: no sorry, no axiom, no
arbitrary choice of functional, and the negative results are theorems about the
actual objects.

## Honest boundary

- The file proves impossibility statements.  It does not construct a
  levelwise additive realification, because none exists.
- The positive content (additiveNormLog, the two levelwise set identities) is on
  the multiplicative group; it does not repair S1961's levelwise equality, it
  identifies exactly what the reduced shell is.
- target_accepted is not claimed (tmp package, no comparator).
- The paper-level comparison (Theta-link / log-volume) is not formalized here;
  this file only fixes the local p-adic/real interface.

## Next executable step

A consumer that needs the S1927 packet should keep using S1961's Q-span
identity; if a levelwise statement is required, it must be stated against
additiveNormLog on K_v^x (levelwise true, see the two set identities), not
against the actual p-adic shell.  The next paper-side object is the
Q-span/volume comparison, not a local realification functional.

## Note on the AUDIT_LEDGER incident (2026-11-01)

Appending this package's ledger entry with a truncating read damaged
AUDIT_LEDGER.md: the DSH read tool returned only the first 385 lines of the
722-line working copy.  The ledger has been restored to the committed version
(commit 61951cd0) plus a repair note, the recoverable fragment (working-copy
lines 660-722) and the S1977 entry; working-copy lines 386-659 are still to be
rebuilt from package reports.  Details and the recovery kit are in
tmp/sheaf/ledger-recovery/README.md.
