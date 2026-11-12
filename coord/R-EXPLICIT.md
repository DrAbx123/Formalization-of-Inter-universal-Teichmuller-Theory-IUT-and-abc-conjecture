# R-EXPLICIT — computing R from tensor-region definitions

Status: source-level partial derivation; no compile. R = -S2717ThetaHullLogVolume = -log Haar(actualC3LogShellTensorRegionL), by S2807.

## 1. Definitions

- C3LogShellTensorBlockL = ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple (Mzk1C3LogShellTensorLActual:44).
- actualC3LogShellL i = integralLogShell at the i-th completion (C3L:65; actualC3LogShellL_eq_integralLogShell:70).
- actualC3LogShellTensorRegionL = tensorIntegralRegion (p := C3L.p) (fun i => shell_i) = finitePadicTensorTprod image of Set.pi univ shell_i (C3L:80; FinitePadicTensorIntegralRegion:20).
- actualC3LogShellTensorHaarL = Measure.addHaar (C3L:100), an arbitrary additive Haar measure, normalized only up to scalar.
- actualC3LogShellTensorLogVolumeL = haarLogVolume haar region (C3L:121).
- R = - actualC3LogShellTensorLogVolumeL (S2807).

## 2. Local Haar formula

For a finite extension K/Q_p with O_K and integral log-shell integralLogShell = (p*)^{-1} log(O_K^×) (IntegralUnitLogarithm:194; logShellScale = p for odd p, p^2 for p=2):

- measure_integralLogShell_eq_index_mul (IntegralLogShellHaarIndex:51):
  mu(integralLogShell) = logShellIntegerIndex (K,p) * mu(O_K).
- integralLogShellDiscrepancy (K,p) = log(logShellIntegerIndex) (:86), and
  discrepancy = log(mu(shell)) - log(mu(O_K)) (:88-100).
- Explicit index (no simpler e/f formula in tree):
  logShellIntegerIndex = card(O_K^× / logShellCongruenceUnits) / card(torsion O_K^×) (discrepancy_eq_log_congruence_sub_log_torsion:108).
  This depends on p, e, f through O_K and the congruence subgroup, but no closed formula in p,e,f is proved.

Thus, with a LOCAL normalization mu_i(O_i)=1:
  mu_i(shell_i) = index_i,  log mu_i(shell_i) = discrepancy_i.

## 3. Tensor region Haar

The tensor region is the IMAGE of the product of local shells under the multilinear map finitePadicTensorTprod, not a product set. Hence

  Haar(region) = (finitePadicTensorTprod)_* (product measure)(region)

and there is no theorem in the tree computing this image measure, its Jacobian/determinant, or a product formula. The file only proves compactness and finiteness.

Consequently the best exact conditional formula is:

  R = - log( product_i index_i ) - log J_tensor
    = - sum_i discrepancy_i - log J_tensor,

where J_tensor is the image-measure scaling of finitePadicTensorTprod (J_tensor=1 only if the map is measure-preserving on the product region, which is NOT proved).

Equivalently, if one normalizes the tensor Haar by the integral region (tensorIntegralRegion itself), then R is not a number but a relative log-volume; the raw Measure.addHaar normalization is arbitrary.

## 4. Exact GAP

1. No normalization theorem for actualC3LogShellTensorHaarL: Measure.addHaar is only unique up to a positive scalar.
2. No change-of-measure/Jacobian theorem for finitePadicTensorTprod.
3. No closed formula for logShellIntegerIndex in terms of e,f,p; only the congruence/torsion index.
4. The local shell is a finite union/index of O_K, so its Haar mass is index_i * mu(O_i); with mu(O_i)=1 it is a finite integer, but the tensor image can collapse/scale.

Therefore an explicit numerical R cannot be derived from the current definitions without those three theorems.

## 5. S1487 concrete data

- S1487Arithmetic l = concreteGaussianInitialThetaArithmeticData l: Fmod = F = K = GaussianField, curve = baseChange GaussianField.
- S1487FivePlace is the Gaussian place above 5; S1487Cand is a chosen q candidate (Classical.choice, finitePlaceQCandidate_nonempty), so its order qOrder is not fixed by the data.
- S1487FaithfulC3 is actualSourcePilotRegionDataL at S1487FivePlace; its tensorIndex/tensorPlaces/tensorTuple are inherited from the source input, not enumerated in S1487.
- For the Gaussian five place: p=5, e=f=1 (split/unramified at 5), so the local O_K is Z_5 and the local shell index is logShellIntegerIndex(Z_5,5), still not numerically evaluated in the tree.
- The 2161 primes do not enter C3LogShellTensorRegionL unless the tensor tuple includes them; qPilotIdeal is a separate arithmetic ideal.

Thus no numeric R for S1487 from the current definitions.

## 6. A and M

A = qPilot.absLogQ = qOrder * log p / (2 l) (or logQ/(2l) weighted).
S1487Cand.order is arbitrary; qOrder is not fixed, so A is symbolic.
With the conditional R formula above:

  M = A - R = qOrder log p/(2l) + sum_i discrepancy_i + log J_tensor.

Sign: the sum_i discrepancy_i >= 0 and log J_tensor is unknown; qOrder >= 1 and log p > 0, so A > 0. The sign of M is NOT determined by current definitions (J_tensor and normalization can dominate).

## 7. Verdict

- Local exact: mu(shell)=index*mu(O), index = logShellIntegerIndex.
- Tensor exact: image measure with unknown J_tensor; no product theorem.
- R numeric: GAP (normalization + tensor image measure + index formula).
- S1487 numeric: GAP (C3 tensor tuple not enumerated; qOrder is a choice).
- M sign: not determined.
- No fake numeric R; all missing pieces are named.
