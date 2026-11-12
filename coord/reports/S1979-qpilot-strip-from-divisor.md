# S1979: the q_v-determined piloted q-pilot strip, its pilot object, and the exact R6 gap

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S1979QPilotStripFromDivisorActual.lean
(582 lines).  Consumer: R6 of LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows,
via S1960's QPilotAnchorIdentification and S1968's paperQPilotDivisor.

## Result

R6 proper splits, in IUT II, Def. 4.9, (viii), into

* (A) the F-prime-strip-with-times-mu identification (what S1960's
  QPilotAnchorIdentification formalizes), and
* (B) the generators of the monoids O^triangleright(-) at the bad places plus the
  local realified value maps rho_v, from which the paper *computes* the associated
  pilot object.

The tree's SourceFTimesMuPrimeStrip has (A) only.  This package constructs (B)
from the actual q_v, proves it is q_v-determined (not blind), identifies the
resulting pilot object with S1968's paperQPilotDivisor, closes R6 at the piloted
level, and proves - rather than asserts - that (A) alone cannot carry (B).

## Constructed (all kernel-checked, no sorry)

1. The O^triangleright(-)-generator of the actual q_v:
   qPilotGeneratorValue D b = -|log q_b|  (<= 0, nonzero, = -(order_b * log 5),
   = Real.log (paperQV D b) = -localLogMagnitude S1487Cand),
   qPilotGenerator D b : SourceHaarActualValueMonoid, an actual element of the
   paper strip's value monoid at the bad rational prime 5 (paperBadPrime).

2. IUT II, Def. 4.9, (viii) as a construction:
   structure PilotedFTimesMuPrimeStrip V Bad (strip + place : Bad -> V +
   generator : forall b, Mon (place b));
   pilotGeneratorRealifiedValue (rho_w(g_w) via the strip's degree map);
   HasNegativePilotGenerator (the "negative arithmetic degree" condition);
   associatedPilotObject D S : IUTIVArithmeticDivisor (PaperFmod D) with
   coefficient -rho_w(g_w) / log q_w at the bad base prime (log q_w from S1968's
   paperBadBasePlace_weight, not hard-wired).

3. Identification with the divisor (S1968):
   associatedPilotObject D (paperQPilotPilotedStrip D) = paperQPilotDivisor D
   (associatedPilotObject_paperStrip);
   coefficient at the bad prime = (paperQVOrder D bad0 : R)
   (associatedPilotObject_apply) - the strip recovers the actual order;
   deg = sourceBadQAbsLog = -paperQPilotLogVolume = |Real.log (paperQV D bad0)|
   (associatedPilotObject_deg_eq_source / _deg_eq_neg_logVolume / _deg_eq_abs_log);
   nonzero (associatedPilotObject_ne_zero).

4. q_v-determination (non-blind):
   qPilotGeneratorLogVolume S = sourceQPilotSignedLog S
   (qPilotGeneratorLogVolume_eq_signedLog), so the pilot degree is the generator
   family's total realified value
   (associatedPilotObject_deg_eq_generatorLogVolume); and
   pilotLevel_not_blind: on the S1487 faithful/two-place pair the (1,0) strips are
   equal (rfl, S1968's candidate_blind) while the generator log-volumes differ
   (-L vs -2L, S1968's qPilot_scalar_differs).  Unlike I.fPrimeStripAt n m, the new
   construction sees the q_v.

5. R6 at the piloted level:
   structure PilotedQPilotAnchorIdentification D S = a
   SourceFTimesMuPrimeStripEquivalence (reducedQPilotTimesMu D)
   S.toSourceFTimesMuPrimeStrip together with generator_compat (isoMon carries the
   anchor's generator to the strip's generator);
   paperQPilotPilotedIdentification inhabits it for the paper strip;
   r6Proper_of_pilotedIdentification gives S1960's unpiloted R6Proper;
   pilotedIdentification_pilotObject: *any* piloted strip carrying the piloted
   identification has associatedPilotObject = paperQPilotDivisor D;
   s1979_r6_piloted packages the three facts.

## The exact first missing (machine-checked, section 7)

* paperQPilotUnitGeneratorStrip D: same SourceFTimesMuPrimeStrip, generators 1.
* It is R6Proper (paperQPilotUnitGeneratorStrip_r6Proper) and its associated pilot
  object is 0 (paperQPilotUnitGeneratorStrip_pilotObject).
* r6Proper_does_not_determine_pilotObject: the q-pilot piloted strip and the
  unit-generator strip have the *same* SourceFTimesMuPrimeStrip (rfl), both are
  R6Proper, and their pilot objects are paperQPilotDivisor D and 0.

Hence the requested paperQPilotFTimesMuStrip D : SourceFTimesMuPrimeStrip PaperV
cannot be produced faithfully: the only honest inhabitant of that type is
paperQPilotStripProjection D = reducedQPilotTimesMu D
(paperQPilotStripProjection_eq_reduced), i.e. S1960 section 5's reduced
self-identification, not R6.  The minimal honest extension is
PilotedFTimesMuPrimeStrip, and the remaining source gap is the paper's literal
O^triangleright(A) subset O^triangleleft(A) submonoid at a universal covering
pro-object of the bad-place split Frobenioid together with its rho_v: here rho_v is
modelled by the strip's degree map and the generator is the actual q_v scalar, not
the Frobenius/unit-theoretic O^triangleright(A).

## Evidence

* Compile: lake env lean -j1 -o .lake/build/.../S1979QPilotStripFromDivisorActual.olean
  -> EXIT 0.  tools/lean_auto.py repair -> status green, exit 0, errors 0,
  forbidden 0 (local compilation + lexical policy only).
* Source SHA256: 13FA1FE814556A9F6403B219549BEAE9012F1E9B4547C52ED0827F43153B72FC
* olean SHA256: 9F485433C3056C19CCA1AF25E3DBBA57B106EE457BBEBC613E573D3BB68C1CBD
  (377496 bytes, .lake/build/lib/lean/tmp/sheaf/xif/paper/).
* Axiom probes (28 declarations): exactly propext, Classical.choice, Quot.sound.
  No sorryAx.
* statement_compiles: yes.  proof_body_checked: yes.  kernel_closed: yes
  (dependency on S1960/S1968/S1927/S1527/S1487 chain; not a full Project build).
  target_accepted: no - the literal paper O^triangleright(A) / rho_v are not
  constructed, and rho_v is modelled by degree.

## Next executable step

Lift PilotedFTimesMuPrimeStrip's generator field to the paper's actual
O^triangleright(A) subset O^triangleleft(A) at a universal covering pro-object
(IUT II, Def. 4.9, (ii)-(iv)) and prove its realified value is the q_v scalar, so
that generator_compat becomes a theorem about Frobenioid data rather than the
q_v scalar model.
