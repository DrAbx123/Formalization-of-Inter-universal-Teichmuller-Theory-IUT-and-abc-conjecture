# C2 targets 2 - strengthened native targets

- Task: R49-C2.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/C2Targets2.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Imports C2Targets; three named sorry targets (G_v action, Kummer arrow, archimedean existence).

## Actual production donors

1. `nativePrimeStripAction (i : X.family.index) (v : NativePlaces X.S)`
   := `(X.family.theater i).primeStrip.action v`.
   Actual production donor `FPrimeStrip.action : Pi v ->* MulAut (Mon v)`;
   theorem `nativePrimeStripAction_actual` is rfl, zero sorry.
2. `NativeArchimedeanBranch` uses the actual native `FPrimeStrip.Mon` at an
   infinite native place; `valueMonoid` is an actual Type, with a proved
   CommMonoid instance, zero sorry.

## Targets with named sorry

- `nativeGvActionTarget2_obligation`: inherited C2Targets conditional
  `SourceLogShellXMuChainActionCompatibility` target; no actual native
  C1-indexed G_v log-shell action/descent donor.
- `nativeKummerArrowTarget i := Nonempty (SourceKummerArrow Unit
  (X.family.theater i).primeStrip (X.family.theater i).primeStrip)`; actual
  production `SourceKummerArrow` over the native prime strip, but no native
  Kummer/root-change inhabitant.
- `nativeArchimedeanBranchTarget := Nonempty (NativeArchimedeanBranch X)`;
  actual source branch type, no actual infinite native selected place constructed.

## Status

statement_compiles true; actual prime-strip action donor and archimedean branch
type actual; target obligations named sorry; no free Type/True.