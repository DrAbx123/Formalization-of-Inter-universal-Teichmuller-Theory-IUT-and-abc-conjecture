# S2510 scheme restrict-scalars self equality: ACTUAL

## BUILT (EXIT=0)
S2510RestrictScalarsActual.lean:
- S2510SchemeRestrict_self: schemeRestrictScalars F F = 1 (SchemeOverField F).
Proof: simp [schemeRestrictScalars, Over.mapId_eq].
Axioms trio; no sorryAx.

## Still missing
- S2510Pseudofunctor_self: (schemeRestrictScalars F F).op.toPseudofunctor = Pseudofunctor.id.
  `rfl` fails; need Pseudofunctor structure equality / identity unitor.
- Fiber equivalence and SourceEtaleStackScalarExtension.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2510RestrictScalarsActual.lean
EXIT=0; SHA256 89987C9999DD8991027C526BBC6C24A16AA74F6527A7413D83433AB9766A42E0
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2510RestrictScalarsActual.olean
olean SHA256: 759EAE351B809085045146BE87ED7023E3FC33475B2383A9417E3F71F8B3D133
axioms: trio