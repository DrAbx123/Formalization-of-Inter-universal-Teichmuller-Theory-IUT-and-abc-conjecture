# S1318: integral capsule with valuation-dependent coefficient ring

Date: 2026-10-30. New Lean file; no modification of
`SourceProcessionCapsuleContract`.

## 1. New structures (not a modification of the old contract)

`tmp/sheaf/xif/paper/S1318IntegralCapsuleZpHomActual.lean` (EXIT=0):

```lean
structure LogShellFamilyZp {VQ : Type uVQ} (R : VQ → Type uR)
    [∀ vQ, CommSemiring (R vQ)]
    (Place : VQ → Type uPlace) (j : Nat) where
  Shell : (i : Capsule j) → (vQ : VQ) → Place vQ → Type uShell
  [addCommMonoid : ∀ i vQ v, AddCommMonoid (Shell i vQ v)]
  [module : ∀ i vQ v, Module (R vQ) (Shell i vQ v)]
```

```lean
structure PolyIsoActionZp ... (L : LogShellFamilyZp R Place j) where
  labelPerm : Capsule j ≃ Capsule j
  shellEquiv : ∀ i vQ v,
    L.Shell i vQ v ≃ₗ[R vQ] L.Shell (labelPerm i) vQ v
```

```lean
structure SourceProcessionCapsuleContractZp (l) (V) (I) where
  procession : Procession ...
  VQ : Type uVQ
  place : VQ → Type uPlace
  [fintypePlace : ∀ vQ, Fintype (place vQ)]
  R : VQ → Type uR
  [commSemiringR : ∀ vQ, CommSemiring (R vQ)]
  logShell : (j) → LogShellFamilyZp R place j.val
  polyIso : (j) → PolyIsoActionZp (logShell j)
```

This is a separate structure; the existing
`SourceProcessionCapsuleContract` (single `R`) is untouched.

## 2. Actual instance

For arbitrary `I : OriginalInput l V` and every actual rational valuation
`vQ : {p // p.Prime}`, actual finite place `v` over `vQ`:

```lean
actualZpR vQ := ℤ_[vQ.1]
actualZpShell vQ v := ↥(integralLogShellLattice
  (K := CommonPrimeCompletion v) (p := vQ.1))
```

with actual instances:

- `CommSemiring (actualZpR vQ)`;
- `AddCommMonoid (actualZpShell vQ v)`;
- `Module (actualZpR vQ) (actualZpShell vQ v)` (via the Submodule structure).

Then:

```lean
actualZpLogShellFamily : LogShellFamilyZp (actualZpR) (actualPlace I) j
actualZpPolyIso : PolyIsoActionZp (actualZpLogShellFamily I j)
  labelPerm := Fin.revPerm
  shellEquiv := -1  -- ℤ_[p]-linear
actualZpCapsuleContract : SourceProcessionCapsuleContractZp l V I
```

Actual fields:

- `R vQ = ℤ_[vQ.1]`, exactly the `p`-adic integer ring;
- `Shell i vQ v = integralLogShellLattice`, the actual integral lattice
  (`Submodule ℤ_[p] K`), not `IQSpan`;
- `VQ` is the actual rational valuations, `place vQ` the actual finite places;
- `polyIso` is a genuine `ℤ_[p]`-linear integral automorphism (not 2-scaling
  over ℚ, not identity-only).

No `A = ℤ` collapse, no `IQSpan`/Q-span, no `PUnit`.

## 3. Exact remaining fields

The new contract captures the paper's valuation-dependent coefficient ring.
Still not constructed:

1. the **tensor packet** over the new contract (the old `TensorPacket` is
   fixed to a single `R`; a `TensorPacketZp` must use `⨂[R vQ]` at each
   valuation);
2. the **distribution equivalence** and its pure-tensor law for that packet;
3. the source identification of `polyIso` with the actual paper
   poly-isomorphism (S1318 only builds an actual integral automorphism, not
   the paper's specific action);
4. compatibility of the actual integral log-shell family with the source
   log-link/Ind actions.

These are downstream, not fields of the contract itself.

## 4. Compile status

```text
lake env lean -j1 -R . -o ... S1318IntegralCapsuleZpHomActual.olean
EXIT=0
```

No `sorry`; file is 148 lines; SHA256
`36A2DD81582D9BF16BD7D18C4615F6E40FC89A04E63D09E12E458E543C7BB963`.

## 5. Conclusion

- Actual valuation-dependent `Z_p` integral capsule contract constructed.
- `R vQ = ℤ_[vQ.1]`, `Shell = integralLogShellLattice`, actual `Module (R vQ)`.
- No simplification by `A=ℤ`, no Q-span/PUnit; old contract unchanged.
- Next exact objects: `TensorPacketZp`/distribution and source polyIso
  identification.
- EXIT=0 report.
