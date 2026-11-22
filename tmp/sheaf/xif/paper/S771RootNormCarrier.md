# S771: carrier decision for qVFamBlock norm

Date: 2026-10-30. Existing coordinate norm equality is not asserted.

## Decision

Introduce the root-norm carrier

  RootNormQVBlock T b

wrapping qVFamTensorBlock T b, with the norm pulled back from rootBase T b
along the one-factor equivalence:

  rootNormLinearEquiv : RootNormQVBlock T b ~ rootBase T b
    := (rootNormEquiv.linearEquiv Qp).trans qVFamBlockLinearEquiv

  SeminormedAddCommGroup RootNormQVBlock :=
    SeminormedAddCommGroup.induced RootNormQVBlock rootBase
      rootNormLinearEquiv.toLinearMap

  NormedSpace Qp RootNormQVBlock :=
    NormedSpace.induced Qp RootNormQVBlock rootBase
      rootNormLinearEquiv.toLinearMap

Then

  rootNormBlockIsometryEquiv : RootNormQVBlock T b ≃ₗᵢ[Qp] rootBase T b

with toLinearEquiv := rootNormLinearEquiv and norm_map' := rfl.

The underlying block map is qVFamBlockLinearEquiv (rootNormBlockIsometryEquiv_apply).

## Rationale

The old qVFamTensorBlock norm is the finitePadicTensor coordinate sup norm;
rootBase uses the spectral norm. These are not identified by the repo, so the
old QVFamBlockNormPreserving is not asserted. The new carrier chooses the
rootBase norm by construction; this makes the isometry definitional/rfl rather
than a fake equality.

No old norm instance is changed, and no spectral/coordinate equality is claimed.
