# Object alignment audit (besides the completion root)

Paper target: -|log(Theta)| >= -|log(q)|.

## Aligned (or mostly aligned)

1. q-pilot parameter: `qVFamily T b` is the actual clause-B q_v;
   `QPilotClassicalLog` uses `order(q_v)*log(p_v)` (IUT III lines 7475-7480).
2. qPilot image point: `QPilotMultiradialImagePoint` was proved equal to the
   actual qVFamily product point (S191/S232).
3. Per-b bad-place indexing and local weights `nativeBadLocalWeight` are
   actual numbers, not toy carriers.
4. Theta labels: `ThetaLabel = {j // 0 < j}` (positive representatives),
   not all `SignedLabel`.
5. Completion Haar on the one-factor local block is actual
   (`Measure.addHaarMeasure` of the closed unit ball).

## NOT aligned / missing

### A. Completion root / mu_{2l}
The paper root q_v^(1/2l) is in K_v.  The tree only has conditional
`HalfRootInCompletion`; the L = rootNormedExtension construction is a
non-paper workaround.  The Q_5 counterexample shows a general completion q
has no 2l-th root.  Root existence is the first blocker.

### B. Local tensor index is one-factor (`qVFamTensorV = Unit`)
The paper uses a tensor over a subset A of {1,...,n_vQ} (usually more than
one factor).  `qVFamTensorV := Unit` collapses it to one factor.  This is a
toy/simplified carrier unless one proves the paper local A is a singleton.

### C. Ind1/Ind2/Ind3 actions
Because of B, `ind1LValued = identity` and the Ind actions are defined on a
singleton packet.  The paper Ind1 reindexes several tensor factors; the
current actions are not the paper ones for a multi-factor A.

### D. q-pilot image mu_log vs classical q-pilot log
`QPilotClassicalLog` is the classical `order*log p`; `QPilotImageMuLog` is
the Haar log of a qUnit hull.  No theorem identifies the two.  The paper
`-|log(q)|` is one object; the tree has two different q-pilot log objects.

### E. Theta hull log vs paper processioned mu_log
`thetaSideObject.hullLog` is a Haar log on the L lambda-O hull;
`thetaSideGlobalProcessionNormalizedLog` multiplies it by the procession
factor and weights, but no theorem identifies it with the paper's
procession-normalized mono-analytic mu_log of the Theta holomorphic hull.

### F. Theta holomorphic hull
The L hull is `singleLambda * unitBall` (a single scaled ball).  No theorem
proves this equals the paper holomorphic hull of the union of possible
Theta images under Ind1/Ind2/Ind3.

### G. O-triangle / log-shell / canonical log(pi)
`OtriangleLogVolumeCompletedObject` uses a formal symbolic log(pi)=(0,1);
canonical log(pi) and full nonunit Haar normalization are still gaps.

### H. Source assembly (cusp, D7, exact sequence splitting)
cusp epsilon realization, D7 per-place local group, and exactSequence
splitting are exact missing source objects.

### I. Norm-ratio / coefficient bridge
The identification of the normalized Theta coefficient with the classical
q-pilot coefficient is not proved; the corrected target is a model
comparison, not the paper target.

## Conclusion

Root is not the only misalignment.  Local tensor one-factor collapse and
Ind actions, q-pilot mu_log identification, Theta hull identification,
O-triangle canonical log(pi), and source assembly are also not aligned.
The existing L/rootTensorBlock objects are auxiliary and cannot be packaged
as the paper Theta side.

### J. S317 completion Theta image is a coefficient surrogate

`S317QPilotThetaSameCompletionBlockActual.completionRootThetaImageSet` uses
`rootThetaImageSet` with coefficient `qVFamPaperRootCoefficient = order/(2l)`.
That is a scaled-region/coefficient surrogate, NOT an actual root-valued
Theta value `(q_v^(1/2l))^(j^2)`.  No actual completion root data is used.
Therefore S317 is a same-type pair, but the Theta side is still a surrogate;
it does not establish the paper Theta object.

## ROOT STATUS CORRECTION (S342)
Completion 2l-root card is false (2l|order contradicts coprime). Paper root lives in O^tri root stack, not Completion/L. All completion-root objects INVALID as paper objects.
