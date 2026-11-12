# S1514: actual canonical Qp-linear surjection from the rational tensor

Date: 2026-10-31.  Lean file: `tmp/sheaf/xif/paper/S1514RationalQpSurjectionActual.lean`.

## Build evidence

- source SHA256: `E1E3270569F5DD40ABE7B906E35A677C32339121D16D6655FF9DFAE0A9BCB25E`
- exit: `0` (`lake env lean -o ... S1514RationalQpSurjectionActual.lean`)
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1514RationalQpSurjectionActual.olean`
- olean SHA256: `6D2C79E5943766CB379F2D9C61E0720151435208FC40AC9F46894B03EC3FC7EF`
- olean size: 816336 bytes
- no `sorry`/`admit`; key `#print axioms` outputs are exactly `propext`,
  `Classical.choice`, `Quot.sound`.

## What is proved

Abstract, for a finite family `M : ι → Type` of `Qp`-vector spaces:

- `baseChangeRightModule`: the right `Qp`-module structure on `V ⊗[Q] Qp`;
- `qTensorToQpTensor : (⨂[Q] i, M i) →ₗ[Q] ⨂[Qp] i, M i`, with pure-tensor formula;
- `canonicalMap : (⨂[Q] i, M i) ⊗[Q] Qp →ₗ[Qp] ⨂[Qp] i, M i`, with
  `canonicalMap (t ⊗ q) = q • qTensorToQpTensor t`;
- `canonicalMap_surjective`, using `PiTensorProduct.span_tprod_eq_top`;
- `canonicalMapQuotientEquiv`, the quotient by the kernel is linearly equivalent
  to the `Qp` tensor (the exact sequence of the comparison);
- `qpAction`, the `Q`-action map `(⨂[Qp] i, M i) ⊗[Q] Qp → ⨂[Qp] i, M i`,
  and the exact kernel description
  `canonicalMap x = 0 ↔ map (qTensorToQpTensor) id x ∈ ker qpAction`
  (`canonicalMap_ker_iff`).

Actual source, for fixed `I`, `l`, `j`, `t : SourceTup I j`:

- `SourceRationalBaseChange j t = SourceLogShellActualIQTensor (sourceDatum I j t) ⊗[Q] Qp`;
- `sourceCanonicalQpMap : SourceRationalBaseChange j t →ₗ[Qp] SourceBlk I j t`, the
  composite of `sourceIQTensorEquiv` with the abstract canonical map;
- `sourceCanonicalQpMap_tprod`, `sourceCanonicalQpMap_surjective`,
  `sourceCanonicalQpMap_range_eq_top`;
- `sourceCanonicalQuotientEquiv`: quotient by the kernel is `SourceBlk`;
- `sourceCanonicalKernel`, `sourceCanonicalKernel_iff` (kernel is the preimage of
  the abstract action kernel), and `sourceCanonicalKernel_contains_rationalRelations`.

No `Qp`-linear equivalence between `SourceRationalBaseChange j t` and
`SourceBlk I j t` is constructed or asserted.  The quotient equivalence is an
equivalence on the quotient, not on the original base change.

## Exact first missing item

The kernel is characterized exactly as the preimage of `ker qpAction`, but a
concrete finite presentation of that action kernel (the `Q`-relations among
the `Qp` pure tensors), or an integral lattice-level comparison, is not
supplied here.  This is the remaining paper-level comparison, not an
equivalence.

## Not run

Comparator, full `LeanFormal` project build, and source-faithfulness review
were not run for this package.
