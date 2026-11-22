# Global equality audit: same-order tautology and 2l root normalization

## 1. The old equality

The old global equality appears in:

- GlobalQVFamThetaHullSumActual.globalQPilotLog_eq_nativeSigned;
- PerBXiFScalarActual.globalThetaHullLog_eq_nativeQVSigned;
- QVFamThetaLatticeHullActual.QVFamThetaHullVsNativeSignedTarget.

In GlobalQVFamThetaHullSumActual both scalars are defined locally as:

  localQPilotLog b = - qVFamilyLatticeCoefficient b * log p_b;
  localThetaHullLogFormula b = - qVFamilyLatticeCoefficient b * log p_b.

They are the same expression, and localQPilotLogEqFormula is rfl. Therefore
the global equality

  globalThetaHullLog = nativeQVPilotNormalizedSignedLogVolume

is an equality of two sums of the same local expression. It is true by
construction, but it is not an independent theta-hull normalization theorem.
It is an "obviously equal" statement: both sides use the same classical-q
order coefficient.

## 2. Root coefficient correction

QVFamRootFactorCorrectionActual gives the exact algebra:

  qVFamPaperRootCoefficient b = order(qVFamily T b) / (2l);
  qVFamTensorCoefficient b = order(qVFamily T b)
    = (2l) * qVFamPaperRootCoefficient b;
  qVFamPaperThetaTensorCoefficient b j
    = (gaussExponent j.1).toNat * qVFamPaperRootCoefficient b;
  qVFamThetaTensorCoefficient b j
    = (gaussExponent j.1).toNat * order(qVFamily T b)
    = (2l) * qVFamPaperThetaTensorCoefficient b j.

Thus the old per-b theta tensor coefficient is exactly 2l times the paper root
coefficient, for every bad place b and every signed label j. The old classical
q coefficient is not the theta root coefficient.

## 3. Number of factors and global normalization

The factor 2l comes from the 2l-th root of q_v, not from a product over the bad
set. Per bad place b the correction is one factor 1/(2l):

  corrected local theta log
    = -(1/(2l)) * order(q) * base_b * log p_b

while the old local theta log is

  old local theta log
    = -order(q) * base_b * log p_b.

The global corrected scalar is therefore

  corrected global theta log
    = sum_b weight_b * corrected local theta log
    = (1/(2l)) * (sum_b weight_b * old local theta log)
    = (1/(2l)) * old global theta log.

It is not (1/(2l))^card(Bad) times the old scalar. The single factor 2l is
counted once globally after summing the local corrections.

If the q-pilot scalar is the classical q scalar, then the corrected theta hull
scalar is smaller in magnitude by exactly the factor 2l:

  corrected theta hull log = (1/(2l)) * q-pilot classical log
  (when the base and weights are the same).

## 4. Too strong or too weak?

The old equality is too strong as a paper theta-hull identity:

- it proves theta hull log = classical q-pilot log;
- the actual paper theta value is q_v^(j^2/(2l)), whose minimal j = 1
  coefficient is order(q)/(2l), not order(q);
- therefore the old theta hull log is larger in magnitude than the corrected
  root theta hull log by exactly 2l.

If one instead divides both the theta and q-pilot scalars by 2l, the equality
would be tautologically restored, but that changes the q-pilot normalization
and is not the original comparison. The correct fix is to use the root
coefficient only on the theta side, while keeping the q-pilot scalar in its
stated normalization.

## 5. What is actual and what is missing

Actual:

- qVFamilyPaperRootCoefficient = order/(2l);
- qVFamTensorCoefficient = 2l * root coefficient;
- qVFamPaperThetaTensorCoefficient = j^2 * root coefficient;
- actual hodgeTwoLthRoot and qVFamilyPaperThetaValueRoot.

Missing actual field:

- an actual normalized theta hull log computed from the root coefficient
  qVFamilyPaperRootCoefficient (or from the root theta value), with actual
  image-hull landing and Haar normalization;
- an actual equality theorem between that root-normalized hull log and the
  paper procession-normalized theta scalar;
- a clear statement of whether the q-pilot side uses the classical q or a root;
  the current nativeQVPilotNormalizedSignedLogVolume uses the classical q
  magnitude.

Until these are supplied, the old global equality should not be consumed as a
paper xi-f identity. It is a valid identity of the classical-q local formula,
but it is too strong for the paper root theta hull and its exact correction is
the factor 1/(2l), applied once globally.

## 6. Decision

- Mark the old equality as a same-order tautology, not a paper theta-hull
  normalization.
- Use the root coefficient c_root = order/(2l) for the paper theta side.
- Apply the 1/(2l) correction once after the global weighted sum, not per bad
  factor.
- Do not divide the q-pilot side unless the paper comparison is explicitly
  changed to a root normalization.
- Keep the actual root objects and the coefficient correction; the missing
  actual is the root-normalized hull scalar equality, not another fake global
  equality.
