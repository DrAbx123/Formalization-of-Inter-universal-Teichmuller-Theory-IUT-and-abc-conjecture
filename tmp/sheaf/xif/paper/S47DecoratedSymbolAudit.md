# S47: decorated F/D prime-strip and script-O audit

Date: 2026-10-29. Lean/source symbol audit only.

## 1. F and D prime-strip decorations

Lean core (PrimeStripCore) has exactly:

* DPrimeStrip V, with Pi, G, proj;
* FPrimeStrip V, which extends DPrimeStrip V and adds Mon, action, degree.

The paper's decoated variants are not separate Lean types:

| Paper signifier | Lean type currently used |
|---|---|
| D-turnstile, D-dashv, D-Theta | same DPrimeStrip V |
| F-Vdash, F-turnstile, F-dashv | same FPrimeStrip V |

Exact collision: every D decoration is represented by the same DPrimeStrip type,
and every F decoration by the same FPrimeStrip type.  There is no decoration
index field, wrapper, or type-level tag distinguishing them in the frozen core.

FPrimeStrip is not an alias of DPrimeStrip: it extends DPrimeStrip, so F and D
are structurally distinct, but the decorations within each family are collapsed.

Necessary actual wrapper (not fabricated here): a decoration-tagged wrapper

  DecoratedDPrimeStrip (δ : DDecoration) V  with strip : DPrimeStrip V
  DecoratedFPrimeStrip (δ : FDecoration) V  with strip : FPrimeStrip V

with separate DDecoration/FDecoration indices for turnstile, dashv, and Theta /
Vdash.  This requires choosing the actual paper decoration for each source
consumer; the tree currently provides no such field, so the exact collision is
reported rather than guessed.

ThetaPilotCarrier/ThetaLinkActual are not prime-strip types and carry no such
decoration; they are separate carriers (see S44).

## 2. O decorations

Actual O objects:

* CompletionIntegers place: the integral ring O of the completion;
* its unit group (CompletionIntegers place)^x is O^x;
* rootsOfUnity n (CompletionIntegers place) is the O^mu root group.

The paper's O-triangle (decorated boundary of the integral structure) has no
dedicated Lean type in the frozen core.  CompletionIntegers, its units, and
rootsOfUnity are distinct carriers by type; they are not aliases of each other.

Exact gap: a dedicated O-triangle carrier/type is missing.  The current
integral-obligation files use CompletionIntegers or integralClosure for O; they
do not encode the boundary decoration.  No wrapper is asserted without the
actual source data.

## 3. Conclusion

The decorated F/D symbols are collapsed at the decoration level: DPrimeStrip and
FPrimeStrip are the only types, so D-turnstile/D-dashv/D-Theta and
F-Vdash/F-turnstile/F-dashv are not separated.  O-boundary decoration is also
absent.  This is recorded as exact collision/gap; no fake wrapper or equality is
introduced.

No sorry, axiom, or True/PUnit.
