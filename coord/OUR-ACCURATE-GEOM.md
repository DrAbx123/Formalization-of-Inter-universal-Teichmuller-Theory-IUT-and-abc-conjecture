# OUR-ACCURATE-GEOM — Haar volume of the C3 tensor region and M = A - R (A1121)

Status: geometric audit; no compile. R = -log Haar(actualC3LogShellTensorRegionL),
by S2807; A = absLogQ >= 0.

## 1. Exact geometric object

- actualC3LogShellTensorRegionL = tensorIntegralRegion (p := C3L.p) of the local
  integralLogShells (Mzk1C3LogShellTensorLActual:80; FinitePadicTensorIntegralRegion:20).
- It is the image of the product of local shells under finitePadicTensorTprod,
  NOT a product set.
- actualC3LogShellTensorHaarL = Measure.addHaar (C3L:100): an arbitrary additive
  Haar measure, unique only up to a positive scalar.
- R = - actualC3LogShellTensorLogVolumeL (S2807).

## 2. Local Haar mass relative to O

For each finite completion K_i/Q_p:
- integralLogShell contains Integers (Integers_subset_integralLogShell).
- measure_integralLogShell_eq_index_mul (IntegralLogShellHaarIndex:51):
    mu(shell_i) = logShellIntegerIndex (K_i,p) * mu(O_i).
- logShellIntegerIndex is a positive integer (logShellIntegerIndex_pos).
- integralLogShellDiscrepancy (IntegralLogShellHaarIndex:86):
    log mu(shell_i) - log mu(O_i) = log index_i >= 0.

Thus, with the LOCAL normalization mu_i(O_i)=1:
    mu_i(shell_i) = index_i >= 1,  log mu_i(shell_i) >= 0.

## 3. Tensor image measure

The tensor region is the image under the multilinear map finitePadicTensorTprod.
No theorem in the tree computes its image measure/Jacobian. Write
    Haar(region) = J_tensor * prod_i index_i
with J_tensor the (unknown) image-measure scaling (J_tensor=1 only if the map is
measure-preserving on the product region, not proved).

Therefore:
    R = - sum_i log index_i - log J_tensor
      = - sum_i discrepancy_i - log J_tensor.

## 4. When is M = A - R >= 0?

M = A + sum_i log index_i + log J_tensor
  = A + sum_i discrepancy_i + log J_tensor.

with A = absLogQ >= 0 (A=0 only qOrder=0; otherwise positive).

Sufficient conditions:

(S1) Normalize the tensor Haar by the integral region (or by the tensor image of
the product of local O_i), and prove that the tensor image is monotone:
    tensorIntegralRegion(O) subset tensorIntegralRegion(shell).
Since shell_i contains O_i, this inclusion holds at the level of product sets and
is preserved by the image map. With Haar(tensor O)=1:
    Haar(region) >= 1  => R <= 0 => M >= A >= 0.
This is the cleanest geometric sufficient condition; it needs only monotonicity
of tensorIntegralRegion, not the unknown J_tensor.

(S2) More generally, prove Haar(region) >= 1 for the chosen normalization; then
R <= 0 and M >= A >= 0.

(S3) Prove Haar(region) >= exp(-A), equivalently R <= A; then M >= 0.

(S4) If local normalization is mu(O_i)=1 and J_tensor >= 1, then R <= 0 and
M >= 0. J_tensor >= 1 is not proved.

Note: if one instead has only the raw Measure.addHaar, none of these is
automatic; the normalization is part of the statement.

## 5. Counterexample risks

1. Raw Measure.addHaar is only unique up to a positive scalar. Scaling Haar by
   c changes R by -log c and M by +log c; the sign of M is NOT invariant under
   this normalization. So M>=0 is not a geometric statement about the raw
   Measure.addHaar alone.
2. The tensor map finitePadicTensorTprod can compress/expand the product measure;
   J_tensor is unknown. Local index_i >= 1 does NOT imply Haar(region) >= 1.
3. If paper normalization uses mu(O)=1 but our S2807 uses raw addHaar, the two R
   differ by the constant log mu(tensor O); an M inequality under one
   normalization does not transfer to the other.
4. Conversely, for any real target one can choose the Haar scalar to force
   M<0 or M>=0; such a statement would be vacuous, not geometric.
5. The hull/ind2 terms are irrelevant to R here: R is the C3 region volume, not
   lana rhs; no gap enters S2807.

## 6. Verdict

- Exact local bound: mu(shell_i)=index_i*mu(O_i), index_i>=1.
- Tensor: Haar(region)=J_tensor*prod index_i, J_tensor unknown.
- M = A - R = A + sum discrepancy_i + log J_tensor.
- Sufficient condition that is actually geometric: normalize Haar by the tensor
  integral region (or tensor O) and prove region contains that normalization set;
  then Haar>=1, R<=0, M>=A>=0.
- Without a normalization theorem, M's sign is not well-defined; raw addHaar can
  be rescaled to change it. This is the main counterexample risk.
- No fake numeric R; the missing normalization/Jacobian theorem is the exact GAP.
