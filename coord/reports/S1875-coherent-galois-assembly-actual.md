# S1875 — assembly of the coherent-cover (Pre)Galois category

Date: 2026-11-01 (session S1875).  Workspace: D:\lean.

## Verdict

* File: `tmp/sheaf/xif/paper/S1875CoherentGaloisAssemblyActual.lean`.
* Build: `lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1875CoherentGaloisAssemblyActual.olean tmp/sheaf/xif/paper/S1875CoherentGaloisAssemblyActual.lean`
  -> **EXIT=0**, no errors, no warnings, no `sorryAx`.
* Source: 27103 bytes, 498 lines, SHA256
  `C4E9C9D79C2FB0EA65C62A59AD2DDA5F1D78986DF590318214601A7154F846FA`.
* Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1875CoherentGaloisAssemblyActual.olean`,
  120032 bytes, SHA256
  `BD5C5B99D4B07C839DF689978D39CD935D7B98B2253248AF58C7077F76C8F3D1`.
* `#print axioms` on every main declaration prints only
  `[propext, Classical.choice, Quot.sound]`.

## What is actually assembled

An actual Mathlib `GaloisCategory` at the target universe:

    S1875GaloisCategory_of_essSurj (h : S1868EssSurj)
      (hIso : S1835BCReflectsIsos) :
      @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01

built from S1868's transported five-field `S1868PreGaloisCategory01` and its
six-field fibre functor `S1868FiberFunctor01` (Omega-fibre at the closed point
(0,0) of Spec R').  Variants: `S1875GaloisCategory` (from
`S1868FirstMissing`), `S1875GaloisCategory_of_coherentAffineEquiv` (from
`S1868CoherentAlgebraFunctor.IsEquivalence`), `S1875GaloisCategory_of_inputs`,
`S1875GaloisCategory_of_inputsEssSurj`.

Five-field intermediates: `S1875PreGaloisCategory_of_essSurj`,
`S1875PreGaloisCategory_of_S1868FirstMissing`,
`S1875PreGaloisCategory_of_coherentAffineEquiv`.

## The direct S1854 / S1857 route and its exact missing

Available unconditionally or from S1856's named first missing:

* `S1875HasTerminal : HasTerminal CoherentCover` (S1854, unconditional);
* `S1875HasPullbacks` / `S1875HasPullbacks_of_firstMissing` (S1857);
* `S1875HasFiniteCoproducts` / `S1875HasFiniteCoproducts_of_firstMissing` (S1857).

Exact missing on this route (`S1875PreGaloisMissing`):

1. quotients by finite groups (`S1875QuotientsByFiniteGroups`);
2. mono induces iso on a direct summand (`S1875MonoDirectSummand`).

`S1875PreGaloisCategory_iff` proves
`PreGaloisCategory C01 ↔ Nonempty S1875PreGaloisMissing` given the S1856
limit inputs; `S1875GaloisCategory_iff` and
`S1875GaloisCategory_iff_missing` do the same for the fibre-functor field.
`S1875PreGaloisMissing_of_essSurj` shows the S1868 route obtains these two
fields under `S1868EssSurj`.

## Precise remaining inputs

For the assembled `GaloisCategory` (S1868 route), exactly two:

1. `S1868EssSurj`: essential surjectivity of the coherent affine comparison
   (`S1868CoherentAlgebraFunctor`).  S1868 now proves fullness
   unconditionally (`S1868Full_proof`, via S1878's `S1878Full_proof`), and
   `S1868FirstMissing_iff_essSurj : S1868FirstMissing ↔ S1868EssSurj`.
2. `S1835BCReflectsIsos`: S1855's field 6 of the algebra-side fibre functor.

For the direct S1854/S1857 route: `S1856PullbackFirstMissing` and
`S1856CoproductFirstMissing` together with the two fields above.  S1867
(`S1867CoherentQuotientsActual.lean`, 7759 bytes at 12:32) is only a generic
colimit-transport skeleton: `S1867HasColimitsOfShape_of_apex` requires the
ambient colimit apexes to be coherent and gives no `Category.{0,1}` field, so
it does not discharge the two fields.

## Inputs and versions used

* S1868 source at compile time: `S1868CoherentFiberActual.lean` 23848 bytes,
  12:45:32, SHA256 `9CEA93AD6A05A646AD956004708B737BE84102BAFAB067421441F477B42D59D4`.
  The S1868 olean actually consumed by S1875 was built earlier from the
  12:39:36 source: 157992 bytes, 12:43:20, SHA256
  `7367204DFFCA9A476107AC7F924BC3207B10FDE958E229BA2C3D3B844A9A3531`.
  S1868 was still being edited at report time; rebuilding S1868 changes the
  dependency and requires rebuilding S1875.
* S1878 olean used by S1868: 172528 bytes, 12:40:20, SHA256
  `D24616704A77D57653DB3FDA22CFF174F71F3261B4149BBE00F2DF56192A6F5F`.
* S1854/S1857 oleans: as built in their sessions; imported unchanged.

## Honest boundary

No fake instance: the `GaloisCategory` is the actual `GaloisCategory.mk`
structure built from S1868's actual PreGalois structure and actual six-field
fibre functor.  It is conditional on the two inputs above; neither is assumed.
No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` in S1875.
The two `S1875...fragment` theorems (trivial action has a colimit; a mono with
initial domain splits) are proved but are only fragments of (G2)/(G3).