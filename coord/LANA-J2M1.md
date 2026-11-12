# LANA-J2M1 — j^2-1 / sFactor-1 / q-pilot base factor in lana (A1120)

Status: grep audit; no compile.

## 1. j^2 - 1 / q-pilot base factor

Grep over tmp/sheaf/lana and tmp/external/ported/lana_tgfree finds NO occurrence of
j^2 - 1, j*j - 1, or sq - 1 in Gap.lean, ThetaRegion.lean, Wall/QPilotRegion.lean.

What is present:
- ThetaRegion.scaleEltAt uses qroot^{(i+1)^2}; scaleElt uses the distinguished label
  (ThetaRegion:126/136).
- Wall/QPilotRegion.lgp_eq_pow (QPilotRegion:139):
  lgp D S = pow D (fun i => (i.1+1)^2) (distinguished) S.
- Wall/QPilotRegion.qRegion (QPilotRegion:314):
  qRegion D = pow D (fun _ => 1) (labOne D) (integralRegion D).
- logVol_pow_integral (QPilotRegion:300):
  logVol (pow D e lab (integralRegion)) = -((sum_i e i)/nC) * absLogQ.

So the q-pilot region is modeled as the theta value for j = 1, exponent 1 in every
capsule, NOT as q^{j^2-1}. The only relation to LGP is in the first capsule:
qRegion_first (QPilotRegion:331) says qRegion at capsule 0 equals lgp(integralRegion)
at capsule 0, because (0+1)^2 = 1. This is a coincidence at j=1, not a subtraction
of a base factor.

Conclusion: lana does NOT subtract the j=1 base factor anywhere; qRegion uses
exponent 1 uniformly, while LGP uses exponent j^2. There is no definition of
q^{j^2-1}.

## 2. ind2Term vs differences of q-pilots

ind2Term (Gap:747) is:
  componentVol(leastHull(thetaComponent)) -
    componentVol(scaleElt • leastHull(shell)).
thetaComponent (ThetaRegion:257) is the union of indAut images of
scaleElt • shell. So ind2Term is the hull enlargement of the theta component over
the scaled shell; it is not a difference of q-pilot objects and contains no
q^{j^2-1}.

gapHullAt (Gap:895) is the weighted sum of ind2Term; gap (Gap:505/523) is the
global hull difference. "Differences of q-pilots" does not appear as a definition
in lana.

## 3. sFactor - 1 occurrences

Inside Wall/WallEquiv:
- Forms.lean:65 and :71: SSIneq iff (sFactor(nC)-1)*absLogQ <= logVol(hull(vcI)).
- VcI.lean:890/897: SSIneq/SSIneqNoHull equivalences with (sFactor(nC)-1)*absLogQ.
- Wall/MultiContainer.lean:88/90/96/344/376: SSIneq definitions and distortion
  bounds with (sFactor(nC)-1)*absLogQ.
- NonDerivable.lean:477, 502, 511, 525, 529, 531, 533: counterexamples and
  non-derivability using (sFactor-1)*a.
- Gap.lean and ThetaRegion.lean: NO sFactor - 1 occurrence.

So sFactor-1 is a wall/SSIneq coefficient, not a term in the gap construction or
theta-region scaling.

## 4. Verdict

- No j^2-1, no q^{j^2-1}, no base-factor subtraction in Gap/ThetaRegion.
- qRegion is j=1 exponent 1 in every capsule; LGP is j^2 in the distinguished label.
- ind2Term is a hull enlargement, not a difference of q-pilots.
- sFactor-1 appears only in SSIneq/wall/counterexample files, never in Gap/ThetaRegion.
- If the paper requires a q^{j^2-1} factor, lana's model does not implement it; this
  is a normalization/modelling gap to record, not a formalized identity.
