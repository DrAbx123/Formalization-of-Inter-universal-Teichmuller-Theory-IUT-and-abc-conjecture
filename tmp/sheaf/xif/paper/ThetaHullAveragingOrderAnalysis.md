# Theta hull log-volume: averaging order and q_v sign

Date: 2026-10-29. Analysis only; no fake inequality.

## Question

For l = 5, the current PaperWeightedThetaSignedActual averages

  (1/|F_l^x|) * sum_{j in F_l^x} j^2
  = (1 + 4 + 4 + 1)/4 = 2.5

and hence produces

  weightedThetaSigned = 2.5 * log(q_v)

while qPilotSigned = log(q_v).  Since q_v < 1, this is more negative
(2.5 log q_v < log q_v), so the claimed direction
weightedThetaSigned >= qPilotSigned is false under that formula.

This note checks the source and the correct order of operations.

## Source evidence

1. Theta values are q_v^{j^2}, not q_v^{-j^2}.
   - IUT I, Example 3.2(iv) / evaluation points: the value of Theta_v at an
     evaluation point with label j is in the mu_{2l}-orbit of
     { q_v^{j^2} } (IUT I text, evaluation-point discussion).
   - IUT III, Definition 3.8(i) and the introduction refer to the theta values
     { q_v^{j^2} }.
   - There is no q_v^{-j^2} in the source; the inverse exponent is not used.

2. q_v is a contraction, not > 1.
   - IUT I, Example 3.2(iv): q_v is the q-parameter of E_v over K_v; the
     chosen q_v is a 2l-th root q_v^{1/2l} in O_Kv, and the q-parameter is
     contracting (|q_v| < 1 in the relevant p-adic normalization).
   - In the present Lean code the actual base q candidate has
     baseQLogMagnitude b = -log ||(baseQ T b).q|| with positive value, so
     ||(baseQ T b).q|| < 1 (qNorm_lt_one).
   - Thus log(q_v) < 0 and the q-pilot signed scalar is negative.

3. The paper object is the hull of the union, then the procession average.
   - IUT III, Corollary 3.12: -|log Theta| is the procession-normalized
     log-volume of the holomorphic hull of the union of possible images,
     where the average is over j in F_l^x.
   - Remark 3.9.5(i): the hull of a region is the **smallest** lambda*O
     containing it, not an average of point volumes.
   - Therefore the order is:
       (a) take the union over labels j;
       (b) take its least lambda*O hull H;
       (c) take log-volume mu_log(H);
       (d) apply the procession average over the copies of H.
   - It is NOT: average the point log-volumes of q_v^{j^2} first and then
     call the average a hull volume.

## Numeric check for l = 5

Take 0 < q_v < 1 and write L = log(q_v) < 0.  For j in F_5^x with centered
representatives +-1, +-2, the signed point logs are

  j = +-1: L
  j = +-2: 4L.

The union of the corresponding scaled regions has hull scale
max(L, 4L) = L (since L < 0).  Hence

  hull log-volume signed = L = log(q_v),
  hull magnitude        = -L = |log(q_v)|,

which equals the q-pilot signed scalar log(q_v), not 2.5 log(q_v).

The arithmetic average

  (1/4)(L + 4L + 4L + L) = 2.5 L

is the average of point log-volumes.  It is not the hull log-volume.  Under
this wrong order the target fails; under the hull-first order the local
identity is

  signed theta hull log-volume = log(q_v).

## Exact corrected scalar formula

For one bad place with actual q_v and actual unit region O normalized so
mu_log(O)=0:

  H(union_j q_v^{j^2} O)
    = lambda_min * O,
  lambda_min
    = max_{j in F_l^x} (j^2 * log(q_v))
    = log(q_v)        because q_v < 1 and j^2 >= 1.

Thus

  -|log Theta|_local
    = mu_log(H(union_j ...))
    = log(q_v)
    = -|log q|_local.

The global F_l^x procession normalization averages copies of this same hull
(or the same hull scalar), so it does not multiply by 2.5.

Equivalently, in positive magnitudes:

  |log Theta|_local = -log(q_v) = |log q|_local,
  and the hull is the **minimum** of the point magnitudes j^2 |log q_v|,
  namely |log q_v|, not the maximum and not the arithmetic average.

## Conclusion

- Theta values: q_v^{j^2}; no inverse exponent.
- q_v: contraction, |q_v| < 1; not > 1.
- The correct operation is hull over the union (extremal in log coordinates),
  then procession average; for l = 5 the local signed result is log(q_v), not
  2.5 log(q_v).
- PaperWeightedThetaSignedActual currently averages point log-volumes before
  taking the hull, so its 2.5 factor is not the paper scalar and its target is
  false for that formula.
- A corrected minimal scalar should take the hull extremum over j first; no
  full IQHullLogVolumeInterface or carrier equivalence is needed for this
  scalar correction.


## 7. Explicit answer on exponent conventions

Checked source paths:

- IUT I, Example 3.2(iv), :3774-3797: q_v is the q-parameter of E_v over K_v, and the chosen element is q_v^{1/2l}; the classical q-parameter is q = e^{2 pi i z} with |q| < 1.
- IUT I, evaluation-point discussion, :6022-6030: the value of Theta_v at an evaluation point with label j is in the mu_{2l}-orbit of
    { q_v^{j^2} }.
- IUT III, Definition 3.8(i), :6506-6544: the Theta-pilot object is indexed by
  j in F_l^*, while the q-pilot object is the object of the global realified
  Frobenioid determined by the collection q_v for v in V_bad.
- IUT III, Corollary 3.12, :10152-10181: the q-pilot log-volume is the log-volume
  of the image of that single q-pilot object, not an F_l^* average of q_v^{j^2}
  terms.

Therefore:

- theta values are q_v^{j^2}, not q_v^{1/j^2} and not q_v^{-j^2};
- q_v is contracting, not > 1;
- the q-pilot side has no j^2 exponent and no F_l^* average of the theta
  values.  Its coefficient is 1 (up to the Remark 3.1.1(ii) place weights).

## 8. Correct order: hull before procession average

For one bad place and one local direct summand, the hull of the union of the
scaled unit regions corresponding to q_v^{j^2} has scale

  lambda = max_{j in F_l^*} (j^2 * log(q_v)) = log(q_v)

because log(q_v) < 0 and j^2 >= 1.  Thus

  signed hull local log-volume = log(q_v)
  positive magnitude            = -log(q_v) = |log q_v|,

which is exactly the q-pilot local signed scalar log(q_v), not
2.5 * log(q_v).

The arithmetic average

  (1/4)(1 + 4 + 4 + 1) log(q_v) = 2.5 log(q_v)

for l = 5 is the average of the point log-volumes.  It is not the hull
log-volume.  Averaging before taking the hull produces the false target; the
correct scalar must take the extremal hull over the union first.

Equivalently, in positive magnitudes the hull chooses the minimum of
j^2 |log q_v|, namely |log q_v| (j = +-1), not the maximum and not the average.

## 9. Consequence

The current PaperWeightedThetaSignedActual formula with coefficient 2.5 is not
the paper scalar.  A corrected minimal scalar should replace the local
F_l^* average by the hull extremum over the union, then apply only the actual
place weights and the procession average over identical hull copies.  No full
IQHullLogVolumeInterface or carrier equivalence is needed for this correction.
