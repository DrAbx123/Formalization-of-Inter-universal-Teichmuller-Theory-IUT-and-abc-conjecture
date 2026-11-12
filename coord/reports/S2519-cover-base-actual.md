# S2519 CoverBase bundle: ACTUAL

## BUILT (EXIT=0)
S2519CoverBaseActual.lean:
structure CoverBase {F} [Field F] (X : HyperbolicOrbicurve F) where
  coverCategory : Category.{u+1,u+1} (OrbicurveFiniteEtaleCover X)
  baseScheme : SchemeOverField F
  basePoint : StrongTrans (schemeRepresentableEtalePseudofunctor F baseScheme) X.stack.fiber.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Donor obstruction
Example36FiberAutomorphism does NOT provide an actual PreGaloisCategory instance; its own header lists
PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op) and FiberFunctor fieldFiber as exact missing instances.
So the donor cannot yet supply PreGaloisCategory or the equivalence transport.

## Next
Build the cover<->finite-etale equivalence (or PreGaloisCategory directly); then Galois core, cover morphisms, fiber data, action.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2519CoverBaseActual.lean
EXIT=0; SHA256 4A14948DFA418A4D679D53E47BD6D5E69E5966D5112F475EFDFF0D7F1C2DF6FC
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2519CoverBaseActual.olean
olean SHA256: 8D1CC4E6151CFD592FF856441E1E61DC94A68C0A1EA67EBCB3D1B0D303D1107D
axioms: trio