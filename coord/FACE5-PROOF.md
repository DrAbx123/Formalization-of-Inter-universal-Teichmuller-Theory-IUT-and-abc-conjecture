# Face 5: proof skeleton and the single remaining construction (A908)

## What is green (machine)

`tmp/sheaf/xif/paper/Mzk1Face5ProofActual.lean` (olean=True):

- `Face5Data` (our framework): `V` (hull log-volume), `A = |log q|/(2l)`, `sF = sFactor(nC)`,
  paper decomposition `V - (sF-1)*A = sumMu + archTerm`, `sumMu >= 0`, `archTerm >= 0`;
- **`face5_inequality_from_perplace`**: `(sF-1)*A <= V` (per-place route);
- `Face5SectionData` (Arakelov difference-bundle data): `degNorm H`, nonzero-section Prop,
  `degNorm H = V - (sF-1)*A`, product formula `degNorm H = sumNorms`, `sumNorms >= 0`;
- **`face5_inequality_of_section`**: `(sF-1)*A <= V` (section/product-formula route);
- `face5_both_routes`, `Face5ConstructionObligation := Nonempty Face5SectionData`.

## The only remaining obligation

`Face5ConstructionObligation`: construct an instance of `Face5SectionData` for the actual
data, i.e. an integral (nonzero) global section `x` of the difference bundle
`H = det(hull) (x) L_q^{ -(sF-1) }` with the arch bound making `sumNorms >= 0`.
Generic existence of such a section is equivalent to the target inequality (qpilot
A903/A904 conclusion), so it is kept as a single explicit construction obligation; it is
NOT a green theorem and is not faked.

## Arakelov interpretation (model note)

`V - (sF-1)*A = degNorm H` is the difference-bundle degree; the per-place terms are
`-log||x||_v` and the arch term is `-log||x||_inf`; the product-formula accounting is the
identity `degNorm H = sum_v (-log||x||_v)`.  lana Arakelov results are referenced only as
cross-check (no import).

## Status

Main theorems green (axioms: propext, Classical.choice, Quot.sound).  Face 5 = skeleton
proved + one explicit construction obligation.  This is NOT a proof of SSIneq/ABC.
