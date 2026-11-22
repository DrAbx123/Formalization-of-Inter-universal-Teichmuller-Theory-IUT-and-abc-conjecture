# S1976 — abstract dagger-F_v G-action: construction, comparison, exact first missing

Date: 2026-11-01
File: tmp/sheaf/xif/paper/S1976AbstractDaggerFActionActual.lean

## Evidence

- Source: 25532 bytes, SHA256 0F1CEA9A97DBA2DFD20C0A57991C8919A6987C35F86DED813DF86541BD1A0F02.
- Build command: lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1976AbstractDaggerFActionActual.olean tmp/sheaf/xif/paper/S1976AbstractDaggerFActionActual.lean
- EXIT=0; build log tmp/sheaf/xif/paper/logs/S1976_compile.log has no error, warning, sorry, or sorryAx.
- Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1976AbstractDaggerFActionActual.olean, 424536 bytes, SHA256 969D6206D3BEEEB402F6A9E9A81B5F0E2C3D6C28C34C0D72E8AE413A8084A29C.
- Consumer: tmp/sheaf/xif/paper/_S1976Consumer.lean, EXIT=0, imports the olean and re-derives the main statements.
- #print axioms on all 16 probed declarations = propext, Classical.choice, Quot.sound only. No sorry/axiom/opaque/True/empty-type/arbitrary inhabitant.

## Result

For an arbitrary FPrimeStrip F and place v:

1. PiActionDescends F v is the condition that the Pi-action on the value monoid is
   constant on the fibres of F.proj v.
2. R1AbstractActionOnDaggerFMissing F v is equivalent to PiActionDescends F v
   (R1AbstractActionOnDaggerFMissing_iff_descends), and the G-action is constructed
   from a proof of descent by choosing preimages (abstractGvActionOfDescends).
3. The compatible G-action is unique (abstractGvAction_unique); the constructed action
   agrees with every section of the projection (abstractGvActionOfDescends_apply_section).
   Thus the preimage choice in (2) is proved irrelevant.
4. The action transports across FPrimeStripEquiv
   (transportAbstractGvAction, nonempty_transport_iff, and the R1 form).
5. The local actual strip S1962R1AbstractActionActual.localFPrimeStrip v has proj = id,
   so its action descends; the construction returns the actual Krull action and equals
   S1962's localAbstractGvAction (localGvActionOfDescends_eq).
   A DaggerFComparison is an FPrimeStripEquiv to the local actual strip; it transports
   the local Krull action to the abstract strip (DaggerFComparison.missing).
6. Non-derivability: a concrete FPrimeStrip over PUnit with Pi = PUnit x MulAut (Z/3),
   G = PUnit, proj = fst, action = snd has no compatible G-action
   (nondescendingFPrimeStrip_noAction).  Its twin with the same DPrimeStrip, the same
   Mon and the same degree but the trivial Pi-action does have one
   (action_not_determined_by_DPrimeStrip).  The two strips are not related by any
   FPrimeStripEquiv (no_equiv_nondescending_descendingTwin).
   Consequently no uniform construction exists for all FPrimeStrip data
   (no_uniform_construction, no_uniform_construction_any_index).

## Exact first missing

For the paper's abstract dagger-F_v the first missing is the source-level datum that
the Pi-action on the value monoid descends along the mono-analytic projection,
equivalently a source G-action whose pullback along proj is the Pi-action
(sourceCondition_iff_exists_sourceAction).  It is present for the local actual strip
as the actual Krull action, but it is not a consequence of the FPrimeStrip interface
or of the D-prime-strip, value monoid, and degree.  For the paper's abstract strip it
must come from the source construction (the dagger-F source input), not from
Definition 3.1 data.

## Not claimed / not run

- Not a construction of the paper's abstract dagger-F carrier itself; no source
  realization of the paper's dagger-F was assumed or fabricated.
- Not run: full project build, comparator acceptance, independent review.
