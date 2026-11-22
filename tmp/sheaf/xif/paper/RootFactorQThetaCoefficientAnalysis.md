# qVFamily order, 2l-root order, q-pilot and theta coefficients

Date: 2026-10-29. Source/formula analysis only; no Lean inequality.

## 1. Source definitions

### 1.1 The classical q-parameter

IUT I, Example 3.2, (iv), pp.61-62 (extraction lines 3774-3797):

  q_v is the q-parameter of the elliptic curve E_v over K_v;
  qroot_v := q_v^(1/2l) is the chosen 2l-th root.

The root is taken in the Kummer extension/algebraic closure, not assumed to lie
in the completion. Its valuation/order is

  ord_v(qroot_v) = ord_v(q_v) / (2l).

The root is determined up to multiplication by a 2l-th root of unity.

### 1.2 The q-pilot object uses q_v, not the root

IUT III, Definition 3.8, (i), p.112 (extraction lines 6731-6769):

- the q-pilot object is determined by the collection of the classical q_v at
  v in V_bad;
- the Theta-pilot object is determined by the theta values
  {q_v^{j^2}}_{j=1,...,l^*}, i.e. by the 2l-th root q_v^(1/2l) raised to j^2,
  up to a 2l-th root of unity.

IUT II, Introduction, pp.2-3 (lines 69-108), states explicitly that the theta
values at l-torsion points are of the form

  qroot_v^{j^2}

up to a 2l-th root of unity, where qroot_v is the 2l-th root of the classical
q-parameter q_v.

Therefore the two pilot objects use two different local coefficients.

## 2. The two local coefficients

Let

  n_v := ord_v(q_v) = (qVFamily T b).order

be the classical q order at the bad place b corresponding to v.

### 2.1 q-pilot coefficient

The q-pilot log uses the classical q_v:

  local q-pilot log = ord_v(q_v) * log(p_v) = n_v * log(p_v).

Ignoring the sign (q_v contracting), the q-pilot local magnitude is

  c_v^q := n_v.

The q-pilot normalized scalar is therefore

  S_q = - sum_v w_v * n_v * log(p_v),

where w_v is the Remark 3.1.1, (ii) weight. No factor 1/(2l) belongs to the
paper q-pilot scalar.

### 2.2 Theta coefficient

The theta value at label j uses the 2l-th root:

  theta_{j,v} = qroot_v^{j^2} = q_v^{j^2/(2l)}.

Its local log is

  log(theta_{j,v})
    = (j^2/(2l)) * ord_v(q_v) * log(p_v)
    = (j^2/(2l)) * n_v * log(p_v).

Thus the Theta-side coefficient is

  c_v^Theta := n_v/(2l),

and the theta tensor coefficient at label j is

  c_{j,v}^Theta := j^2 * n_v/(2l).

This is the actual correction: the Theta coefficient is not n_v; it is
n_v/(2l).

## 3. The 2l-root/hodge relation

The actual algebraic-closure root

  hodgeTwoLthRoot T b

satisfies

  (hodgeTwoLthRoot T b)^(2l) = qVAlgClosedUnit T b,

where qVAlgClosedUnit is unitToAlgClosed (qVUnit T b). On valuations/orders
this gives

  ord(hodgeTwoLthRoot T b) = n_v/(2l)

in the Kummer extension. The chosen root is determined only up to the actual
mu_{2l} root set:

  hodgeTwoLthRoot' = zeta * hodgeTwoLthRoot,  zeta^(2l) = 1.

The mu ambiguity multiplies theta values by zeta^(j^2), but it does not change
the local log-magnitude/order n_v/(2l); in particular it does not change the
scalar coefficient c_v^Theta or c_v^q.

The project formula file QVFamRootFactorCorrectionActual records the exact
comparison:

  qVFamTensorCoefficient T b
    = (2*l.value) * qVFamPaperRootCoefficient T b,

where

  qVFamPaperRootCoefficient T b = n_v/(2l).

Thus the old QVFamTensorCoefficientActual coefficient n_v is the classical
q coefficient, not the Theta coefficient.

## 4. Which scalar uses which coefficient

For the paper objects:

1. q-pilot scalar -|log(q)| uses the classical q_v:
   coefficient c_v^q = n_v.
   Do not divide by 2l.
2. Theta-pilot scalar -|log(Theta)| uses the theta values
   qroot_v^{j^2}: coefficient c_{j,v}^Theta = j^2 * n_v/(2l).
   Do not use the classical n_v without the 1/(2l) factor.
3. Root-corrected q-side scalar, if one defines it by replacing the
   classical q log with the root log, uses c_v = n_v/(2l). This is a different
   scalar from the paper q-pilot scalar, related by

     S_q = (2l) * S_{q,root}.

   It must not be substituted for -|log(q)| in Corollary 3.12.

The actual file RootCorrectedQPilotScalarActual proves

  nativeQVPilotNormalizedSignedLogVolume T
    = (2*l.value) * qVPilotRootNormalizedSignedLogVolume T.

This identity is correct as a relation between the classical q scalar and the
root-normalized scalar. It does not say that the paper q-pilot scalar is the
root-normalized one. The paper q-pilot scalar is the classical n_v version.

## 5. Correct assignment summary

| object | local coefficient | use |
|---|---|---|
| q-pilot -|log(q)| | n_v = ord(q_v) | classical q_v |
| Theta-pilot theta value j | j^2 * n_v/(2l) | root qroot_v^{j^2} |
| root-normalized q-side scalar (auxiliary) | n_v/(2l) | not the paper q-pilot scalar |

Equivalently:

  c^q_v = n_v,
  c^Theta_{j,v} = j^2 * n_v/(2l) = j^2 * c^q_v/(2l).

The factor 2l belongs between the classical q-pilot coefficient and the
root-based Theta coefficient. It does not belong inside the classical q-pilot
scalar itself.

## 6. References

- IUT I, Example 3.2, (iv), pp.61-62: extraction lines 3774-3797.
- IUT II, Introduction, pp.2-3: lines 69-108.
- IUT II, Remark 2.5.1, pp.72-73: lines 4356-4396.
- IUT III, Definition 3.8, (i), p.112: lines 6731-6769.
- IUT III, Corollary 3.12, pp.173-174: lines 10499-10529.
- Project: QVFamTensorCoefficientActual.lean,
  qVFamTensorCoefficient, qVFamThetaTensorCoefficient.
- Project: QVFamRootFactorCorrectionActual.lean,
  qVFamPaperRootCoefficient,
  qVFamTensorCoefficient_eq_twoL_mul_rootCoefficient.
- Project: TwoLthRootKummerActual.lean, hodgeTwoLthRoot,
  hodgeTwoLthRoot_pow, twoLthRoot_ratio_mem_mu.
- Project: RootCorrectedQPilotScalarActual.lean,
  qVPilotRootNormalizedSignedLogVolume,
  nativeQVPilotNormalizedSignedLogVolume_eq_twoL_mul_root.
