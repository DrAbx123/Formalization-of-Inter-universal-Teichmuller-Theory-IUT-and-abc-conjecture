# Paper-object audit: RootExtensionProductCarrier / PaperSignedHull

## What is actual

* rootNormedExtension T b = IntermediateField.adjoin K {root},
  where root^(2l) = unitToAlgClosed(qUnit) in AlgebraicClosure(K).
  This is an actual finite extension field containing a chosen 2l-root.
* RootExtensionProductCarrier = (b : Bad) -> rootNormedExtension T b.
* rootExtensionProductHaar = Measure.pi of local Haars on these L_b.
* rootExtensionProductImageHull = coordinatewise closed norm balls.
* rootExtensionProductImageHullLog = Haar log relative to product unit ball.

## Why this is NOT yet a paper object

1. Paper q[2u] lives in the extension/root stack with mu_{2l}
   indeterminacy; the Lean carrier fixes ONE chosen root in an
   IntermediateField.  There is no root-stack/groupoid or mu_{2l} orbit
   quotient in RootExtensionProductCarrier.
2. The paper Theta hull is a holomorphic hull / lambda-O region on
   O^triangle; rootExtensionProductImageHull is an artificial coordinatewise
   closed norm ball.  It is not proved equal to the paper holomorphic hull.
3. rootExtensionProductHaar is Haar on the product of the chosen L_b fields.
   It is not proved to be the paper root-stack/product Haar on the
   mu_{2l}-orbit carrier.
4. PaperSignedHull is a project interface (IQHullLogVolumeInterface),
   not a literal paper object; its ambient/procession fields are exact
   source obligations.

## Consequence

These are actual model objects and may be useful, but they are NOT yet
paper-faithful.  Do not claim the extension product hull/log or
PaperSignedHull as the paper Theta object without a root-stack/mu_{2l}
and holomorphic-hull bridge.
