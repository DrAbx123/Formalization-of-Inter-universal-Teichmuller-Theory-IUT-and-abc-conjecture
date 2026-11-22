import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic
/-! Distinguished scalar theta_{b,j} = alpha_b^{j^2} and its normalized order.

If `alpha^(2*l) = q`, then `ord (alpha^(j^2)) = (j^2/(2*l)) * ord q`.
The source-level torsion rationality and Tate comparison are recorded as the remaining
construction; this file proves the actual order identity with a self-contained `ord`. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
/-- Normalized order `ord_p x = -log ||x|| / log p`. -/
def ord {K : Type*} [Norm K] (p : Nat) (x : K) : Real :=
  -Real.log ‖x‖ / Real.log p
/-- The distinguished theta value at exponent `j`. -/
def theta {K : Type*} [Field K] (alpha : K) (j : Nat) : K :=
  alpha ^ (j ^ 2 : Nat)
/-- `ord (alpha ^ n) = n * ord alpha`. -/
theorem ord_pow {K : Type*} [NormedField K] (p : Nat) (alpha : K) (n : Nat) :
    ord (K := K) p ((alpha : K) ^ n) = (n : Real) * ord (K := K) p alpha := by
  unfold ord
  rw [norm_pow, Real.log_pow]
  ring
/-- Actual order identity for `theta_{b,j}`. -/
theorem ord_theta {K : Type*} [NormedField K]
    {p l : Nat} (alpha q : K) (j : Nat) (hl : l ≠ 0)
    (hroot : alpha ^ (2 * l) = q) :
    ord (K := K) p (theta alpha j) =
      ((j : Real) ^ 2 / (2 * (l : Real))) * ord (K := K) p q := by
  have htheta : ord (K := K) p (theta alpha j) = ((j : Real) ^ 2) * ord (K := K) p alpha := by
    unfold theta
    rw [ord_pow (K := K)]
    congr 1
    norm_num [pow_two]
  have hq : ord (K := K) p q = (2 * (l : Real)) * ord (K := K) p alpha := by
    rw [← hroot, ord_pow]
    congr 1
    push_cast
    ring
  rw [htheta, hq]
  have hl' : (l : Real) ≠ 0 := by exact_mod_cast hl
  field_simp [hl']
/-- Source-level distinguished scalar data: the actual theta root and q at a fixed prime. -/
structure DistinguishedScalarData (p : Nat) (K : Type*) [NormedField K] where
  alpha : K
  q : K
  alpha_ne_zero : alpha ≠ 0
  l : Nat
  j : Nat
  l_ne_zero : l ≠ 0
  root_eq : alpha ^ (2 * l) = q
/-- The order of the distinguished theta value. -/
theorem distinguished_theta_order {p : Nat} {K : Type*} [NormedField K]
    (X : DistinguishedScalarData p K) :
    ord (K := K) p (theta X.alpha X.j) =
      ((X.j : Real) ^ 2 / (2 * (X.l : Real))) * ord (K := K) p X.q :=
  ord_theta X.alpha X.q X.j X.l_ne_zero X.root_eq
/-- Exact source gap: E[2l]-rationality + K_v transport + Tate comparison give the root
`alpha^(2*l)=q` in the actual local field. -/
def torsionToLocalRootGap : List String :=
  [ "E[2l] rational over K via SourceClauseC.torsion23_rational/representation_eq_canonical",
    "transport to K_v via kernel_field_identification",
    "Tate comparison q_comparison gives alpha in K_v with alpha^(2*l)=q" ]
theorem torsionToLocalRootGap_length : torsionToLocalRootGap.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1BoxDistinguishedScalarActual
end
