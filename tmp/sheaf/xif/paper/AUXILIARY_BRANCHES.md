# 鸡肋 / auxiliary branches (do not treat as paper target)

User instruction: do not be clever; if a branch is a workaround that changes the
paper's carrier, it is auxiliary and must not be used to claim xi-f.

## A. Root-extension tower (L = rootNormedExtension)

Paper IUT I, line 3707 says: q_v admits a 2l-th root in O^⊵(T_X^Kv), using the
2-torsion assumption (Definition 3.1(b)).  The source has
`PuncturedEllipticCurve.Torsion23Rational` / `torsion23_rational`.

Therefore the paper root lives in the completion K_v, NOT in an algebraic
closure extension.  The whole L = rootNormedExtension tower
(`rootNormedExtension`, `RootL`, `RootBaseLZeta`, rootTensorBlock as L-valued,
root-extension Haars, root-extension lambda-O hulls, rootHaarFactor) is a
WORKAROUND for the missing proof of root existence in K_v.  It is auxiliary.

Correct next object: actual 2l-th root of qVFamily q in the completion,
derived from the source 2-torsion data.  Then Theta values q_v^(j^2) live in
the SAME completion tensor block as qPilot; no carrier equivalence is needed.

## B. Transported qPilot Haar / product CLE

`qPilotTransportedAmbientHaar`, `S232QPilotHaarTransportActual`,
`S247QPilotHaarInstancesActual`, `S280QPilotBlockCLEActual`,
`S304/S306` transported Haar: auxiliary comparison objects.
The qPilot image already has an actual Haar on its own carrier
(`QPilotMultiradialAmbientHaar`, `Measure.pi`).  Do not use transported Haar
normalization as the paper object.

## C. UnifiedCarrier / RootBaseLZeta

`UnifiedCarrier = qVFamTensorBlock ⊗_Qp RootBaseLZeta` double-counts K0 and
has dimension dim(K0)*dim(L).  It is not the paper tensor packet.  Auxiliary
only; do not use for comparison.

## D. Haar factor norm^d for arbitrary lambda

`rootHaarFactor`, `thetaScalingHaarFactor`, `norm^d` formulas are useful for
the lambda-O scaling of a chosen normalized Haar, but they are auxiliary
normalization identities, not the xi-f comparison.  Do not make them target
dependencies.

## E. Duplicate normalized logs

`sourceQTensorHullNormalizedLog` (source tensor normalized mass) and qside
`thetaSideObject.hullLog` (Haar lambda-O hull on rootTensorBlock) are two
different models.  Pick one final Theta log; do not assert an unproved
equality between them.  The final Theta log should be the actual hull log in
the paper carrier (completion block once the root is in K_v).

## Final target remains

  -|log(Theta)| >= -|log(q)|

with both sides in the same paper carrier.  No workaround carrier may be
substituted.
