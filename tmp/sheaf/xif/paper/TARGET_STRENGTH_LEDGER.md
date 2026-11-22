# Target Strength Ledger

Purpose: stop asking the user to say stronger/weaker.  Every candidate target is
checked against IUT III Corollary 3.12 directly.

## Exact paper target

IUT III, Cor 3.12 (corpus lines 10324-10353): write

  -|log(Theta)|  = procession-normalized mono-analytic log-volume of the
                   holomorphic hull of the union of possible images of a
                   Theta-pilot object, relative to Kummer isomorphisms, in the
                   multiradial representation, subject to (Ind1),(Ind2),(Ind3);

  -|log(q)|      = procession-normalized mono-analytic log-volume of the image
                   of a q-pilot object, without (Ind1),(Ind2),(Ind3).

Conclusion:

  -|log(Theta)| >= -|log(q)|.

In positive-magnitude form (ThetaMag=|-logTheta|, QMag=|-log q|):

  ThetaMag <= QMag.

The final Lean target must be this actual inequality, with actual paper objects
and genuine mu_log, with no correction term and no extra source hypothesis
beyond the paper input.

## Classification

### Too strong / false (must reject)

- label-sum hull: sum over all SignedLabel of -log theta; false for q<1 and
  sum j^2 > 1 (CorrectedHullCounterexampleActual).
- hull enclosure giving the opposite signed direction.
- qParameter power q^(j^2) used as paper theta when q is the q-parameter; the
  paper theta uses the double-underlined 2l-th root.
- identifying qParameter and qRoot as one object.

### Too weak (must not be final)

- hull = unitBall with definitional log 0.
- comparison carrying normRatioCorrection / thetaHullCoefficientCorrection.
- source conditions NormRatioOneSourceCondition, HalfRootInCompletion,
  QVFamNormInstanceGap, RootHullScalingFormulaAt used as assumptions.
- Dirac counting measure as mu_log.
- closure of finite image (measure zero) as paper holomorphic hull.

### Exact / acceptable as final

- actual holomorphic hull of the union/possible images under Ind1,Ind2,Ind3;
- actual product Haar mu_log on that hull;
- actual q-pilot image Haar mu_log;
- procession normalization;
- ThetaMag <= QMag (equivalently -|logTheta| >= -|log q|) with no correction
  and no extra assumptions.

## Gate

Any theorem offered as paper-level xi-f is rejected if it contains any of:

  correction term, unitBall-as-hull, Dirac-as-mu_log, conditional source Prop,
  qParameter-as-paper-theta, different inequality direction.

Intermediate theorems may be kept as lemmas with explicit names, but cannot be
renamed paperXiF or counted as target acceptance.

## Current path judgement

The existing ActualPaperXiFTarget proof is NOT the paper target: it is the
normalized qVFam/root-hull inequality.  The new B-path is still missing the
actual extension-valued hull, its genuine product mu_log, Ind1/Ind3 image
actions, and correction elimination.  Therefore no paper-level completion is
claimed.

## Self-check rule

Before reporting progress, classify each new theorem as one of:
  PROVED-EXACT, PROVED-INTERMEDIATE, CONDITIONAL, GAP, REJECTED.
Only PROVED-EXACT may be called paper-level.  The user does not need to point
out weak targets; weak results are labeled intermediate automatically.

## Normalization-consistency rule (do not bridge two Haar normalizations)

The paper compares log-volumes in ONE procession-normalized mono-analytic
mu_log.  It does not require the spectral normalized norm and the default
valuation norm on a completion to be equal.

`qVFamNormalizedNorm` is the spectral normalized norm used by
`qVFamNormalizedCoefficient` and the normalized mu_log.  `qVFamDefaultNorm` is
the default valuation norm.  The ratio `qVFamNormRatio` and the resulting
normRatioCorrection are artifacts of mixing the two normalizations.  Such a
bridge is (a) not required by Cor. 3.12, and (b) may be false.

Therefore:
- do NOT make `QVFamNormInstanceGap` / `qVFamNormRatio = 1` a dependency of the
  paper target;
- define the q-pilot log-volume with the SAME normalized mu_log as the Theta
  hull (use `qVFamNormalizedNorm` / normalized measure);
- then the normRatioCorrection vanishes by construction, not by a false bridge.
- `QVFamNormInstanceGap` may remain only as a diagnostic comparing two model
  normalizations.

## CORRECTION to the normalization-consistency rule (paper check)

IUT III, corpus line 7475-7476, defines explicitly

  log(q) := ord_v(q_v) * log(p_v).

So the q-pilot log-volume is the CLASSICAL local valuation log, not the
spectral-normalized norm.  The bridge

  qVFamNormalizedCoefficient = order(q_v) * rationalDegree

is therefore NOT an artifact of mixing two normalizations; it is needed to
identify the normalized Theta-side coefficient with the paper's classical
q-pilot log.  The earlier rule saying to avoid this bridge was too broad.

The real problem is different: if the equality fails, then the choice of
`qVFamNormalizedGenerator` / normalized norm is inconsistent with the paper's
q-pilot normalization.  The fix is to choose/prove the normalized generator
norm = p^(-(order*degree)) (or adjust the coefficient definition), not to
replace the q-pilot log by an arbitrary normalized norm.

## Q-pilot definition rule (reject normalized-coefficient substitution)

IUT III lines 7475-7480 define

  log(q) := ord_v(q_v) * log(p_v).

This is the classical local valuation log of the q-parameter.  It is NOT the
spectral normalized coefficient c_norm.  Therefore any target that defines

  processionNormalizedQPilotLog := sum_b w_b * (c_norm_b * log p_b)

and calls it the paper q-pilot is only a MODEL comparison unless the exact
identity

  c_norm_b * log p_b = ord_v(q_v) * log(residueNormBase)

is proved.  `BadPlaceProcessionNormalizedComparisonActual` is therefore an
intermediate model comparison, not the paper xi-f target.

Do not remove the normRatio correction by redefining q-pilot.  Prove the
coefficient identity or keep the correction/target gap explicit.

## Object-first rule (user instruction)

Do not prove the xi-f inequality until both sides are completely constructed.
An inequality between partial/conditional/surrogate objects is a useless gap.

### Theta side must be complete

1. actual Theta-pilot possible images (all labels, root-valued q_v^(j^2));
2. mu_{2l} indeterminacy action on those images;
3. Ind1/Ind2/Ind3 actions and the union of possible images;
4. actual holomorphic hull (lambda-O scaling hull / closure as appropriate);
5. actual product Haar and normalized mu_log;
6. procession normalization.

### q side must be complete

1. actual q-pilot object from the local q-parameters q_v
   (single-underlined q_v, v in V_bad);
2. classical log(q)=ord_v(q_v)*log(p_v);
3. q-pilot image in the multiradial representation;
4. actual Haar/mu_log on that image;
5. procession normalization.

Only after these objects are constructed may the comparison

  -|log(Theta)| >= -|log(q)|

be stated.  Conditional inequalities, correction targets, model comparisons,
and source-field-conditional targets are not the paper target.

## FALSE OVER-STRENGTHENING (confirmed by S342)

The proposition

  exists r in Completion K_v, r^(2l) = q_v

is STRICTLY STRONGER than the paper and is FALSE for the actual qVFamily.

S342 proves:
  qVFamilyTwoLRootCard_impossible : not Nonempty (QVFamilyTwoLRootCard)
  natRootSystem_impossible : not Nonempty (NatRootSystem (qVUnit T b))

Reason: a completion root forces (2l) | order(q), hence l | order(q),
contradicting clause (c) Coprime(order(q), l).  This is not a missing Kummer/
Hensel input; the strengthened statement is false.

The paper root q_v^(1/2l) lives in the orbifold structural sheaf / root stack
O^{tri}(T_x) = O^⊵, not as a completion element.  Constructing the completion
root is a forbidden shortcut.

All files depending on PaperQRootCard / PaperCompletionThetaValue are INVALID
as paper objects and must not be used in target dependencies.
