# S757: QVFamBlockLinearEquiv isometry attempt

Date: 2026-10-30. Conditional isometry; norm equality is exact gap.

## Condition

QVFamBlockNormPreserving T b :=
  forall x, ||x||_qVFamTensorBlock = ||qVFamBlockLinearEquiv x||_rootBase.

## Conditional actual isometry

qVFamBlockLinearIsometryEquiv hpres :
  qVFamTensorBlock T b ≃ₗᵢ[Q_p] rootBase T b
with toLinearEquiv := qVFamBlockLinearEquiv T b, norm_map' := hpres.

qVFamBlockLinearIsometryEquiv_norm_map states the norm equality.

## Exact norm-instance gap

QVFamBlockNormEqualityRequired := QVFamBlockNormPreserving T b.

The domain norm is the FinitePadicTensor coordinate norm
(finitePadicTensorCoordinates / finitePadicTensorNormedAddCommGroup); the
codomain norm is the spectral normalized-completion norm
(normalizedCompletionNontriviallyNormedField / spectralNorm).

No Mathlib or repo theorem currently identifies these two norm instances.
No isometry is asserted without hpres.

No fake norm/isometry.
