# Brandt matrix experiment (A876, path alpha) — NOT EXECUTED

Status: this session did NOT run the computation.  No numerical data is reported and no
conclusion about path alpha is drawn; fabricating data is prohibited.  What is delivered:
a data interface (Lean) + the exact experimental protocol below.

## Protocol (ROUTES 12.3(a))

1. For each prime conductor N < 10^5 (curves E of prime conductor N):
   - compute the supersingular isogeny graph at p (Brandt matrix B(p) on X_0(N)-new part);
   - extract the primitive integral eigenvector v of the relevant Hecke operator;
   - test the pairing identity `||v||^2 = delta * e_p` (norm of v vs modular degree delta
     times local factor e_p).
2. Graph invariants to record: spectral gap of the adjacency operator, delocalization
   (inverse participation ratio) of v; correlation with `||v||^2/delta`.
3. Deflation criterion (12.3(c)): if the smallness of `||v||^2/delta` is explained only by
   level lowering and has no correlation with graph invariants, the route is rejected.

## Lean interface

`tmp/sheaf/xif/paper/Mzk1BrandtExperimentInterfaceActual.lean` (green):
- `BrandtExperimentData` fields (conductor, matrix entries, eigenvector, normSq, delta,
  ramification, pairingIdentity Prop, spectralGap, delocalization);
- `DeflationCriterion` fields (`loweringExplains`, `graphInvariantExplains`, `rejection`);
- `DataAdmissible` sanity predicate; `brandtRows` status table.
All numeric fields are DATA to be filled by the external computation; none is asserted.

## Conclusion on path alpha

Open / not evaluated.  Required next step: run the protocol on an external CAS and
transcribe the resulting tables into `BrandtExperimentData` instances; then evaluate the
deflation criterion.  No new mechanism from alpha is claimed.
