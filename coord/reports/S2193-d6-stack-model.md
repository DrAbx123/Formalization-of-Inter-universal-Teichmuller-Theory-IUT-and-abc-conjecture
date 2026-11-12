# S2193: representable D6 stack candidate / exact IsStack bridge

Date: 2026-11-02. Layer: **O** (source orbicurve D6). No target change,
no fake, independent of 3.11/Eta.

## Files read

- `tmp/sheaf/xif/paper/S2188D6RealizationActual.lean`
- `Iut/Foundations/Orbicurve.lean`
  (`EtaleStackOverField`, `EtaleStackPseudofunctor`,
  `schemeRepresentableFiberFunctor`, `IsStack`)
- `tmp/sheaf/xif/paper/S2057RootStackThetaPilotActual.lean`
  (finite root-stack scalar/KummerRootStack groupoid; not an EtaleStack)
- `LeanFormal/IUT/IUTII/Frobenioid/Example36OrbicurveFeasibility.lean`
  (`MissingD6GeometricRealization`)
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceEtaleStackInstanceSupplyReduction.lean`
  (one-point fiber; no nontrivial stack)
- reports `S2188-d6-realization.md`, `S2177-sign-quotient-xf.md`

## Source object / domain / direction

- Source object: `S2188D6Realization A`, equivalently
  `MissingD6GeometricRealization A.F`.
- Domain: original O-layer; no SourceCompletion/FirstMissing assumption.
- Direction: test the representable-stack route and the S2057 root-stack route;
  construct the actual representable fiber and isolate the exact missing
  effective-descent bridge.

## Deliverable

`tmp/sheaf/xif/paper/S2193D6RealizationModelActual.lean`

```text
EXIT=0
olean=YES
lines=68
SHA256=CF0A99E72A26563B3D563FE494436700440A3B1B9D768F7B3E672916F3652183
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2193D6RealizationModelActual.olean
axioms: propext, Classical.choice, Quot.sound
```

## BUILT

1. `S2193RepresentableFiber F X`:
   `(Iut.schemeRepresentableFiberFunctor F X).toPseudofunctor'`
   — the actual representable pseudofunctor associated to a scheme over F.
2. `S2193RepresentableIsStack F X`:
   `(S2193RepresentableFiber F X).IsStack (SchemeOverField.etaleTopology F)`.
3. `s2193RepresentableIsStack_iff`: definitional restatement.
4. `S2193RepresentableStack F`: `scheme : SchemeOverField F` plus
   `isStack`; no inhabitant.
5. `S2193RepresentableStackRequired F := Nonempty (...)`.
6. `S2193RepresentableFiberComponent F`: scheme, IsStack, nondegeneracy;
   no inhabitant.

## Exact first missing (representable route)

```text
S2193RepresentableIsStack F X
  = (S2193RepresentableFiber F X).IsStack
      (Iut.SchemeOverField.etaleTopology F)
```

and for the full D6 carrier:

```text
scheme : Iut.SchemeOverField F
isStack : S2193RepresentableIsStack F scheme
nondegenerate : ¬ IsPointFiber (S2193RepresentableFiber F scheme)
curvePointRealization for A.curve
```

No inhabitant is asserted; in particular no `IsStack` instance for the
representable fiber is fabricated.

## Required Mathlib bridge

Mathlib 4.32.2 provides:

```text
Pseudofunctor.IsStack (Pseudofunctor.IsStackFor)
```

as a class/predicate, and the tree's terminal/point fiber proofs
(`IsStack.of_isStackFor`) for the constant point fiber. There is no theorem or
instance in Mathlib/tree:

```text
representable fiber -> Pseudofunctor.IsStack etaleTopology
```

i.e. no bridge from a representable presheaf of categories (or a sheaf of
sets/discrete categories) to the effective-descent predicate for the big etale
topology on `SchemeOverField F`. Constructing that bridge is the exact missing
API.

## S2057 root-stack route

`S2057RootStackThetaPilotActual` constructs:

- the real finite root-stack scalar `rootStackTheta` on q[2u];
- the `KummerRootStack` action groupoid / `RootSet` and `RootStackMu`;
- scalar power `rootStackTheta^(2l) = paperQNorm`.

This is a finite root-stack/Kummer groupoid over the finite root-stack
extension, **not** an `Iut.EtaleStackPseudofunctor F` over
`SchemeOverField F`, and it carries no `Pseudofunctor.IsStack` for the big
etale topology. It cannot supply the D6 `fiber` field without a new bridge
from the root-stack groupoid to a category-valued etale stack. No such bridge is
constructed in the tree.

## Rejected fake routes

- terminal constant fiber: `orbicurveSignature = none`, no geometry, point
  fiber;
- `sourceStackPointEtaleFiber`: point fiber, cannot surject onto a curve with
  two distinct points;
- inserting `some sourceTypeOneOne` into a point fiber: metadata only;
- S2057 root-stack scalar/groupoid: not an etale stack over
  `SchemeOverField F`;
- declaring `IsStack` as a field/axiom: not done.

## Consumer

If `S2193RepresentableIsStack F X` and the nondegeneracy/curve-point data are
supplied, `S2193RepresentableStack F` gives the D6 fiber and then
`S2188D6Realization A` (with curve fixed) gives xF/xF_geometry. No 3.11/Eta
assumption.

## Next executable subgoal

```text
prove (schemeRepresentableFiberFunctor F X).toPseudofunctor'
  .IsStack (SchemeOverField.etaleTopology F)
```

for an actual `X : SchemeOverField F` with nontrivial geometry, or construct a
direct category-valued quotient stack with effective descent.

## Reports read

`coord/reports/S2188-d6-realization.md`,
`coord/reports/S2177-sign-quotient-xf.md`, plus the S2057 root-stack and
one-point fiber audits above.
