# S1352: theta function/line bundle — named exact obligations

Date: 2026-10-30.  Target: `tmp/sheaf/xif/paper/ThetaFunctionLineBundleActual.lean`.

## Result

* Mirror: `tmp/sheaf/xif/paper/S1352ThetaFunctionExact.lean`, EXIT=0, SHA256
  `C1A1C02239589D151B164ABF324A0B49D6E8B7E874FB69785112029A43B12C22`.
* Landed: the original file is byte-identical to the mirror (same SHA256).
  Original compile: EXIT=0 (olean rebuilt 22:00:47).
* No `sorry`, no `axiom`, no `Nonempty` in the code; the only repaired
  structure left is the pre-existing actual-data structure
  `ActualQThetaValueData`, whose fields are actual theta data and their
  equations (not free `Prop` fields).

## What was removed

The former

```lean
structure ThetaFunctionLineBundleMissing (S : SourceDefinition31Data.{u} l) where
  curveLineBundle : Prop
  thetaObject : Prop
  thetaFunction : Prop
  thetaGlobalSection : Prop
  thetaZeroDivisorEq : Prop
  qPilotDivisor : Prop
  thetaLinkIdentification : Prop

def MissingThetaFunctionLineBundle : Prop :=
  Nonempty (ThetaFunctionLineBundleMissing (S := S))
```

is a forbidden weak interface: seven free `Prop` fields and a `Nonempty`
gate, inhabited by `⟨True, …⟩`, asserting nothing.

## What replaced it

Seven named exact obligations, with no propositional field and no gate:

```lean
inductive ThetaFunctionLineBundleObligation : Type
  | curveLineBundle | thetaObject | thetaFunction | thetaGlobalSection
  | thetaZeroDivisorEq | qPilotDivisor | thetaLinkIdentification
```

plus the exact list `thetaFunctionLineBundleObligations`, its length theorem
(`= 7`, `rfl`), the type alias `ThetaFunctionLineBundleObligations`, the
actual list `actualThetaFunctionLineBundleObligations`, and the boundary
theorem `thetaFunctionLineBundle_available_is_divisor_only` (divisor type,
zero-degree zero divisor, and list length 7).

Actual divisor-level and q_v data are unchanged: `actualThetaCurve`,
`actualThetaDivisorType`, `actualThetaZeroDivisor` and its degree/Galois
theorems, the full real principal divisor and product formula,
`ActualQThetaValueData`, `actualQThetaValueData`/`...Concrete`, the theta
zero locus and its emptiness proof.

## Why the obligations are named data, not invented `Prop` statements

There is no line-bundle, theta-object, theta-function or Theta-link API for the
actual Weierstrass curve in Mathlib 4.32.2 or in the tree: the curve is not a
`Scheme` here, Mathlib has no invertible-sheaf/line-bundle theory for
Weierstrass curves, and the tree's own audits
(`SourceQlThetaLineBundleObstruction`, `Example36SourceEtaleThetaTheory`,
S1323) record these as exact missing datum with no formal type.  A `Prop` body
would therefore be either `True`-like or a fabricated carrier.  The named
enumeration follows the accepted exact-missing pattern of S1323/S1320: the
seven paper items are named exactly and nothing is asserted or faked.  No line
bundle is constructed.

## Consumers

The four references to the removed interface were updated to the exact list
`ThetaFunctionLineBundleObligations` (a `Type`, not a gate):

* `SourceCurveThetaLineBundleActual.lean`
* `SourceThetaLineBundleActual.lean`
* `ThetaPilotArithmeticDivisorActual.lean` (former `Nonempty` use removed)
* `ThetaPilotSourceThetaDivisorActual.lean`

These consumer files were already stale uncompiled files before this change:
they have no oleans, some dependencies have no oleans
(`ThetaLineBundleAnalyticActual`, `GlobalThetaPilotLogVolumeActual`), and
`SourceCurveThetaLineBundleActual` has pre-existing API errors (e.g.
`actualSourceCurveCoordinateRing S`) and warnings; `ThetaPilot*` call sites
also supply `T.tuple.source : SourceSignQuotientData` where
`SourceDefinition31Data` is expected.  Those defects are independent of S1352
and were not repaired here; the four edits only keep the interface reference
consistent with the new named obligations.

## Axioms

Probe (`#print axioms`, EXIT=0) for the new declarations and the actual data
theorems: only `propext`, `Classical.choice`, `Quot.sound`.

## Status

* statement_compiles: yes (mirror and landed file EXIT=0).
* proof_body_checked: boundary/length theorems are kernel-checked; the seven
  geometric obligations are unproved by design (named exact datum).
* kernel_closed: only for the boundary theorems; the theta line
  bundle/function/section/divisor/q-pilot/Theta-link objects remain open.
* target_accepted: false.  The source geometric theta package is still missing.

## Next step

To turn the seven names into `Prop` obligations with content, supply the
missing geometric API (line bundle/sheaf of modules on the actual Weierstrass
curve, or the `TateInverseJUniformization` interface with an olean) and state
the theta section/divisor identification on that API.  Do not fill the names
with `True`, `PUnit` or an arbitrary carrier.

Stale staging files `S1335ThetaFunctionFix.lean` and `_S1328TFLProbe.lean`
still contain the old weak structure; they are not in the compile queue or in
the consumer chain and are superseded by this change.
