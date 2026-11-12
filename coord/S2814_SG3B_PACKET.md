# S2814 / SG3b — local packet for the C3 tensor log-volume

Date: 2026-11-07
Status: **partial ACTUAL**: local packet definition and its log-volume are
actual; the tensor-region packet identity is the exact missing statement.

## File

`tmp/sheaf/xif/paper/S2814SG3bLocalPacketActual.lean`

```text
src 5253 B
SHA256 13ffc20566cf9745e471db4999b3490821de0912c4d55086a9b05f9a57702ac8
olean 75232 B
SHA256 ca6af3c48f9152dac2cec887413d5b7fbd79276bbc9713747f2d6df2c8269e58
EXIT=0
AXIOMS [propext, Classical.choice, Quot.sound]
QUEUED
```

## 1. Product decomposition of the region

`actualC3LogShellTensorRegion` is by definition

```lean
tensorIntegralRegion (p := C3.p)
  (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
  (fun i => actualC3LogShell C3 i)
```

and `FinitePadicTensorIntegralRegion` proves

```lean
theorem tensorIntegralRegion_eq_range (M) (S) :
    tensorIntegralRegion M S =
      Set.range (fun x : ((i) → S i) =>
        finitePadicTensorTprod M (fun i => (x i).val))
```

So at the level of **sets**, the tensor integral region is the image of the
product of the local log-shells under the multilinear tensor map.

Attempting to state this directly for the C3 block hit a technical coercion
issue: `C3LogShellTensorBlock` is `ArithmeticTensorTupleBlock`, while
`tensorIntegralRegion` returns a subset of `FinitePadicTensor`; the needed
`CoeT (Set (FinitePadicTensor ...)) ... (Set (C3LogShellTensorBlock ...))`
is not synthesized (typeclass timeout).  This is a statement-level blocker, not
a mathematical counterexample.

## 2. Actual local packet

Local Haar log-volume:

```lean
noncomputable def S2814LocalLogVolume (C3) (i : C3.tensorIndex) : Real :=
  (haarLogVolume Measure.addHaar (actualC3LogShell C3 i)).toReal
```

Positive local scale and packet:

```lean
noncomputable def S2814LocalScale (C3) (i) : Real :=
  Real.exp (S2814LocalLogVolume C3 i)

noncomputable def S2814LocalPacket (C3) :
    PositivePacket C3.tensorIndex where
  scale := S2814LocalScale C3
  positive := S2814LocalScale_pos C3
```

Actual computation:

```lean
theorem S2814_packetLogVolume_eq_sum_localLogVolume (C3) :
    packetLogVolume (S2814LocalPacket C3) =
      ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i
```

Axioms trio.

## 3. Exact missing packet identity

```lean
def S2814TensorPacketIdentity (C3) : Prop :=
  actualC3LogShellTensorLogVolume C3 =
    ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i
```

Conditional consumer:

```lean
theorem S2814_packetIdentity_of_tensorIdentity (C3)
    (h : S2814TensorPacketIdentity C3) :
    actualC3LogShellTensorLogVolume C3 =
      packetLogVolume (S2814LocalPacket C3)
```

This is the SG3b target, stated but **not proved**.

## 4. Why the identity is missing

1. `tensorIntegralRegion` is an image of a product under the **multilinear**
   `finitePadicTensorTprod`; it is not a Cartesian product region.  Haar measure
   does not automatically factor through a multilinear image.
2. No theorem in the tree proves
   `volume (tensorIntegralRegion ...) = product of local volumes`
   (or the corresponding log-volume sum).  `FinitePadicTensorLogShellHull`
   gives positivity/finiteness of the hull measure, not a product formula.
3. `actualC3LogShellTensorLogVolume` is defined directly as
   `(haarLogVolume (actualC3LogShellTensorHaar C3)
      (actualC3LogShellTensorRegion C3)).toReal`; it has no local-scale
   decomposition.
4. The finite positive-packet determinant identities in
   `HullDeterminantLogVolumeReduction` are actual only for abstract
   `PositivePacket` diagonal matrices; they do not identify the C3 tensor Haar
   measure with a packet determinant.

## 5. What would close SG3b

Either:

- prove the product (Fubini/Kronecker) formula for the Haar measure of
  `tensorIntegralRegion` under `finitePadicTensorTprod`, including the
  normalization factor, and identify the log of that factor with the sum of the
  local log-volumes; or
- construct a different actual C3 packet whose scale factors are the local
  log-shell Haar volumes and prove directly that its region has the same Haar
  log-volume.

Until then, do not assert `S2814TensorPacketIdentity`.

## 6. Actual exact factor formula available

The finite fractional-lattice model has the exact normalized Haar formula
(re-exported in the same file as
`S2818_normalizedLogVolume_fractionalLattice`):

```lean
theorem S2818_normalizedLogVolume_fractionalLattice
    (places) (tuple) (mu) [IsAddHaarMeasure mu]
    {c : iota -> Real}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple mu
      ((F c * O_hol : Submodule Z_p ...) : Set ...) =
      -((sum_i c i) * Real.log (p : Real))
```

So for the fractional-lattice model the normalization factor is exactly
`1 / finrank` in `arithmeticTupleNormalizedLogVolume`, and the local exponents
`c i` sum to the total log-volume.  Axioms trio.

This is the closest actual factor formula, but `actualC3LogShellTensorRegion`
is a tensor image of **log-shells**, not `(F c) * O_hol`; the formula does not
apply without a new identification.

Other actual facts inspected:

- `FinitePadicTensorIntegralRegion.tensorIntegralRegion_eq_range`: the region
  is the image of a product under the multilinear tensor map (set-level product,
  no measure factorization).
- `FinitePadicTensorLogShellHull.measure_tensorLogShellHull_pos_lt_top`: only
  positivity/finiteness of the hull measure.
- `FinitePadicTensorLogShellRealization.exists_realized_tensorLogShell_hull`:
  field-product realization of the hull, with scales `lam`; no product volume
  formula.
- `FinitePlaceIntegralTensorCovolume.arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`:
  exact relative Haar log of the integral log **lattice** via intersection
  indices, not of the tensor log-shell region itself.
- `FinitePlaceSelectedPrimeIntegralTensorVolume.*`: exact weighted lattice
  volumes; lattice, not `actualC3LogShellTensorRegion`.

First precise blocker for the C3 tensor identity: there is no theorem
`mu (e '' tensorLogShellRegion) = ∏ local volumes` (or its log-sum), and
`tensorLogShellRegion` is only a subset of the integral log lattice.  The tensor
map is multilinear, so the missing normalization factor is not supplied by any
current actual theorem.

## 7. Relation to SG3a

SG3a reduces the upper gap to the SG3a packet identity
`actualC3LogShellTensorLogVolume = packetLogVolume packet`.
SG3b supplies the natural local packet and shows that this identity is exactly
the missing tensor-volume product formula.  No fake packet or axiom is used.
