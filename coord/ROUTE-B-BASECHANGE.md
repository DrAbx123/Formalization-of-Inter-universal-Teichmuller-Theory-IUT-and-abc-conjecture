# ROUTE-B-BASECHANGE — C3 block base-changed to the root extension (A1065)

Status: design only; no Lean file written/compiled.  Resolves A1062: qroot is in
the finite extension `rootNormedExtension`, not in the C3 base completion.

## 1. Existing carriers

- `RootExtension (G) v := AlgebraicClosure (CommonPrimeCompletion (G.place v))`
  (`PaperC3ThetaRootActual:35`); algebraic closure, not a finite extension.
- `rootNormedExtension T b := IntermediateField.adjoin (rootBase T b) {rootNormedElement}`
  (`PaperRootCompletionTensorActual:58`); a **finite** IntermediateField over
  `rootBase T b := NormalizedCompletion (qVFamTensorPlace T b)` (`PaperThetaRootObstruction:41`).
- `rootNormedUnit : (rootNormedExtension T b)ˣ` (`PaperRootCompletionTensorActual:120`).
- `rootNormedElement_pow : rootNormedElement^(2l) = unitToAlgClosed sourceRootQUnit`
  (`:72`).
- `PaperRootExtensionEquivActual.rootExtensionEquivRingEquiv (v) :
  RootExtension (G) v ≃+* SourceAlgebraicClosure (G.place v).val` (`:39`),
  identity on the common algebraic closure; `rootExtensionEquivUnits` (`:48`).
  This is an algebraic-closure carrier equivalence, not a finite-completion map.
- C3 block: `C3LogShellTensorBlockL := ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple`
  (`Mzk1C3LogShellTensorLActual:44`), fibers `CommonPrimeCompletion (C3LogShellPlaceL i)`
  (`:40`).

## 2. Base-changed block (design)

Route B replaces the base completion `C3LogShellFiberL i` by the finite extension
`L_i := rootNormedExtension T (e i)` for a place map
`e : C3L.tensorIndex → Bad (nativePlaceSelection T)` (or a selected subset).

New definitions:

```lean
-- base completion identification (new datum)
structure BaseCompletionEquiv
    (C3L : SourcePilotRegionDataL) (T : SourceNativeInitialThetaData l)
    (e : C3L.tensorIndex → Bad (nativePlaceSelection T)) where
  baseEquiv : ∀ i, rootBase T (e i) ≃+* CommonPrimeCompletion (C3LogShellPlaceL C3L i)

-- finite root extension at each factor
abbrev RootFiber (e i) := rootNormedExtension T (e i)

-- base-changed tensor block
abbrev C3RootBlock := FinitePadicTensor (p := C3L.p) (fun i => RootFiber (e i))
```

Requirements/instances:
- `rootNormedExtension` is a `NontriviallyNormedField`, `NormedAlgebra ℚ_[p]`,
  `FiniteDimensional ℚ_[p]`, `CompleteSpace`, `IsUltrametricDist` (available in
  `PaperRootCompletionTensorActual` for the relevant `T,b`; need re-index by `e i`);
- `ArithmeticTensorTupleBlock` / `FinitePadicTensor` ring, algebra and continuous
  multiplication instances (`FinitePadicTensorFieldDecomposition:25/28/77`);
- `C3RootBlock` has a Haar measure `Measure.addHaar`, compact integral region,
  and a finite-dimensional `ℚ_[p]`-vector-space structure.

## 3. Place map (main GAP)

The C3 tensor index is a tuple of places of `Fmod`; the qroot lives at a place of
`T.arithmetic.F` (`qVFamTensorPlace`).  Required:

1. a map `e : C3L.tensorIndex → Bad (nativePlaceSelection T)` (or a choice of
   factor per qroot label/place), respecting the label/tuple structure;
2. `BaseCompletionEquiv` identifying `NormalizedCompletion (qVFamTensorPlace T (e i))`
   with `CommonPrimeCompletion (C3LogShellPlaceL C3L i)`;
3. compatibility of the base-change with the tensor integral region/local
   log-shell (`actualC3LogShellL`).

No such map/equivalence exists today (`ROOT-COMPLETION-MAP.md`).

## 4. qroot scaling on the base-changed block

Let `u_i := rootNormedUnit T (e i) : (RootFiber e i)ˣ`.  The tensor unit
`u := ⨂_i u_i` acts by multiplication on `C3RootBlock` (ring structure).  Define
the q-pilot region as
```lean
def qPilotBaseChangedRegion := (u : C3RootBlock) • rootThetaRegion
```
with `rootThetaRegion` the base-changed integral log-shell region
`tensorIntegralRegion` of the `actualC3LogShellL` images.

Haar scaling law needed:
```lean
theorem haarLogVolume_mul_unit
    (u : (C3RootBlock)ˣ) (S : Set C3RootBlock) :
    haarLogVolume (Measure.addHaar) (u • S) =
      haarLogVolume (Measure.addHaar) S + log (distribHaarChar u)
```
or the equivalent multiplicative Haar character form.  Available pieces:
- `FinitePadicHaarScaling.measure_prime_smul_finiteDimensional` (`:25`),
  `log_measure_prime_smul_finiteDimensional` (`:54`) for prime scalars;
- `arithmeticTupleNormalizedLogVolume_primeScalar_zpow` (`:510`) for prime powers;
- general unit `distribHaarChar` law is in Mathlib/`ScaleVolume` (port batch L),
  not yet specialised to `C3RootBlock`.

## 5. Dependencies / port batches

Route B does **not** need the lana C3 definitions if the base-changed block is
built from our LeanFormal `FinitePadicTensor` and `rootNormedExtension`; it needs:

| component | source | batch |
|---|---|---|
| `FinitePadicTensor`, `ArithmeticTensorTupleBlock` | LeanFormal green | none |
| `rootNormedExtension`, `rootNormedUnit` | `PaperRootCompletionTensorActual` | none |
| `rootExtensionEquivRingEquiv` | `PaperRootExtensionEquivActual` | none |
| `tensorIntegralRegion`, local `integralLogShell` | LeanFormal green | none |
| general unit Haar scaling | Mathlib `distribHaarChar` / lana `ScaleVolume` | L (port) |
| `incl`/`scaleEltAt`/`scaleElt` if matching paper tensor factors | lana Packet/ThetaRegion | L (incl) / C (scaleElt copy) |
| `leastHull`/`componentVol`/`logShellRadius` | lana Gap/VcI | C copy |
| `factorAut`/`tensorAut`/`indAut` | lana IndAut | L |
| `ordp_qrootOf` | lana Data | C/T copy |
| `vcI/vcIComp/hullOf` | lana Ind3/Rss | C copy |

Route B is independent of the TG-blocked Wall files only if it avoids
`leastHull`/`componentVol`/`vcI`; the base-changed region uses our additive tensor
Haar instead, and only needs the Haar scaling lemma (batch L).

## 6. Minimal declaration list for Route B

1. `BaseCompletionEquiv` (base completion identification);
2. `placeMap : C3L.tensorIndex → Bad (nativePlaceSelection T)`;
3. `RootFiber`, `C3RootBlock` (base-changed tensor block);
4. `rootThetaRegion` (base-changed integral region);
5. `qPilotBaseChangedRegion u`;
6. `haarLogVolume_mul_unit` (general unit scaling on the base-changed block);
7. `qPilotBaseChangedVolume : haarLogVolume = -A` (target theorem);
8. `thetaSubsetQPilot` target in the base-changed carrier.

## 7. Verdict

- Route B is type-correct in principle: base-change the finite extension
  `rootNormedExtension`, not the algebraic closure `RootExtension`.
- The hard part is the place map/base completion equivalence `e`
  (`BaseCompletionEquiv`), which is absent.
- The Haar scaling law can reuse Mathlib `distribHaarChar`/lana `ScaleVolume`
  (batch L); no TG dependency is required for the base-changed block itself.
- If `e` is supplied, the qroot unit is a genuine element of the base-changed
  block and the region is `u • O`, not a fake linear equivalence.
