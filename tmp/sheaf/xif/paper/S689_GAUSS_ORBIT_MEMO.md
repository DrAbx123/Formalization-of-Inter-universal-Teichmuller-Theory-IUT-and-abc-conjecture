# S689: finite Fourier / quadratic Gauss experiment on Theta labels

Status: numerical/symbolic experiment only; no paper theorem asserted.
Related compiled tool file: S684QuadraticGaussFiniteActual.lean.

## Objects tested

For odd prime l, N = 2l, zeta = exp(2*pi*I/N):

* quadratic Gauss sum  G_l(a) = sum_{j in ZMod N} zeta^(a*j^2)
* mu_2l orbit average  A_j = (1/N) * sum_{m in ZMod N} zeta^(m*j^2)
* theta magnitudes    theta_j = q^(j^2/(2l)), q = 1/5
* product exponent    E_l = (1/(2l)) * sum_{j=1}^{l-1} j^2

## Numerical results

l=5, N=10, N mod 4 = 2:
G(odd a)=0; G(even a)= +-sqrt(20); |G|^2=20=2N=4l.
mu-orbit average A_j=0 for j=1,2,3,4.
theta sum (j=-2..2) = 3.75329; signed sum = 0.34793; q^(1/(2l))=0.85134.

l=7, N=14:
G(odd a)=0; |G(even a)|=sqrt(28), |G|^2=28=4l.
A_j=0 for j=1..6.
theta sum = 4.75628; signed sum = -0.23074; q^(1/(2l))=0.89140.

l=11, N=22:
G(odd a)=0; |G(even a)|=sqrt(44), |G|^2=44=4l.
A_j=0 for j=1..10.
theta sum = 6.32847; signed sum = -0.10241; q^(1/(2l))=0.92946.

## Exact pattern (candidate statements)

1. For N=2l with l odd:
   G_l(a)=0 if a is odd.
   |G_l(a)|^2 = 4l if a is even and l does not divide a.
   Pairing j with j+l cancels odd a; even a reduces to 2 times
   the quadratic Gauss sum over F_l, magnitude sqrt(l).

2. For 0 < j < l:
   (1/(2l)) * sum_{m=0}^{2l-1} zeta^(m*j^2) = 0,
   because 2l does not divide j^2.

3. Therefore the mu_2l-orbit average of the paper root theta value
   (zeta*q)^(j^2) is q^(j^2) * A_j = 0,
   not q^(j^2), and not a positive normalization.

4. Product identity:
   prod_{j=1}^{l-1} q^(j^2/(2l)) = q^((l-1)(2l-1)/12)
   using sum j^2 = l(l-1)(2l-1)/6.

## Conclusion: negative for the hoped-for diagonalization

Finite Fourier/Gauss does NOT give an identity of the form
  average over mu_2l of Theta = normalized positive Theta
nor a bound Theta-average <= q-magnitude.

* Averaging over mu_2l annihilates every nonzero Theta label exactly.
* The quadratic Gauss sum is supported only on even additive frequencies and
  has constant modulus sqrt(4l); it is a phase-cancellation object, not a
  positive volume estimate.
* q^(j^2) is a quadratic phase, not a multiplicative character, so Mathlib's
  gaussSum theory for MulChar does not directly apply; only the finite
  quadratic exponential can be summed.
* The useful normalization is the already-known coefficient-level 1/(2l):
  paperRootCoefficient = order(q_v)/(2l), not a Gauss-sum average.

## Candidate Lean statements (not asserted as paper theorems)

  -- Candidate: odd frequency vanishes
  theorem quadraticGaussSum_odd_frequency_eq_zero
      (l : Nat) (hl : Nat.Prime l) (hodd : l % 2 = 1)
      (psi : AddChar (ZMod (2*l)) Complex)
      (hpsi : forall x, psi x = Complex.exp (2 * Real.pi * Complex.I * x / (2*l)))
      (a : ZMod (2*l)) (ha : a.val % 2 = 1) :
      quadraticGaussSum l psi a = 0 := by
    sorry

  -- Candidate: even nonzero frequency has squared modulus 4l
  theorem quadraticGaussSum_even_frequency_norm_sq
      (l : Nat) (hl : Nat.Prime l) (hodd : l % 2 = 1)
      (psi : AddChar (ZMod (2*l)) Complex)
      (hpsi : forall x, psi x = Complex.exp (2 * Real.pi * Complex.I * x / (2*l)))
      (a : ZMod (2*l)) (ha : a.val % 2 = 0) (hla : (a.val / 2) % l != 0) :
      Complex.normSq (quadraticGaussSum l psi a) = 4*l := by
    sorry

  -- Candidate: mu_2l orbit average vanishes for nonzero theta label
  theorem mu2lOrbitAverage_eq_zero
      (l : Nat) (hl : Nat.Prime l) (hodd : l % 2 = 1)
      (j : Nat) (hj : 0 < j) (hjl : j < l) :
      (1 / (2*l) : Complex) *
        Finset.univ.sum (fun m : ZMod (2*l) =>
          Complex.exp (2 * Real.pi * Complex.I * (m.val * j^2) / (2*l))) = 0 := by
    sorry

  -- Candidate: product exponent identity
  theorem thetaProductExponent (l : Nat) :
      (Finset.range l).sum (fun j => (j+1 : Real)^2) / (2*l) =
        ((l-1)*(2*l-1) : Real) / 12 := by
    sorry

These are candidates only; the first three require a concrete primitive additive
character and are not compiled. The last is elementary and can be proved from
the sum-of-squares formula.

## Recommendation

Do not build further theta comparison on a Gauss-sum / mu_2l diagonalization.
Use the actual coefficient normalization (paperRootCoefficient = order/(2l))
and the actual root magnitude (rootThetaMagnitudeValue), and target the
q-pilot comparison directly. The only exact identity from this experiment is
the product exponent E_l; it does not imply any q-pilot bound.