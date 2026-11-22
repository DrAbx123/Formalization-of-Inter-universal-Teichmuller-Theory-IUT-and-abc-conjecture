# S702 memo: QPilotRegionNormExactGoal candidate computation

Exact Lean target (S687):

```lean
QPilotRegionNormExactGoal (l) T b cNorm := forall x in qPilotClassicalRegion (qVFamTensorPlaces T b) qVFamTensorTuple cNorm, norm x <= (rootImageRadius T b : Real)
```

## Data at a bad place b
- p = qVFamTensorP T b
- N = (qVFamily T b).order : Nat
- 2l = 2 * l.value

The qVFam block is the one-factor p-adic tensor ArithmeticTensorTupleBlock at the unique place qVFamTensorPlace T b.
For one factor the fractional lattice is the norm ball F(c) = { x : norm x <= p^(-c) }.
The holomorphic lattice O_hol is the integral closure, hence its norm is <= 1.
Therefore qPilotClassicalRegion = F(c_norm) * O_hol, c_norm = N, is contained in the norm ball of radius

```text
R_region = p^(-N).
```

## Root image radius candidate
The actual root theta magnitude is the 2l-th root of q_v:

```text
norm(q[2u]) = norm(q_v)^(1/(2l)) = p^(-N/(2l)).
```

At positive theta label j = 1, j^2 = 1, so

```text
rootImageRadius = sup_j norm(q[2u]^(j^2)) = p^(-N/(2l))
```
(the maximum is at j=1 because the negative exponent is largest for j^2=1).

## Candidate inequality
```text
p^(-N) <= p^(-N/(2l))
```
because p > 1 and

```text
-N <= -N/(2l)    (2l >= 1, N >= 0).
```
Hence the candidate region radius is below the candidate root image radius:

```text
R_region <= rootImageRadius,
R_region / rootImageRadius = p^(-N(1 - 1/(2l))) <= 1.
```

## Exact remaining formalization
The numerical computation uses two unformalized identifications:
1. one-factor fractional lattice norm radius: x in F(c) -> norm x <= p^(-c);
2. root image radius closed form: rootImageRadius = p^(-N/(2l)).
These are the exact two statements needed to turn the candidate into QPilotRegionNormExactGoal.
No Lean proof of either closed form is asserted here.

## Candidate predicate
```lean
def QPilotRegionNormCandidate : Prop :=
  (qVFamTensorP T b : Real) ^ (-(N : Int)) <=
    Real.rpow (qVFamTensorP T b : Real) (-(N : Real) / (2 * l.value))
```
This candidate inequality is arithmetic; it does not assert the lattice/radius identifications above.