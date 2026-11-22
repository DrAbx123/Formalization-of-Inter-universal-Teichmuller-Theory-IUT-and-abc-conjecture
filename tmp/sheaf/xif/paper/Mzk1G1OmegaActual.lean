/- G1-B Fermat Omega actual: the actual absolute differential module of the affine
Fermat chart A0 = k[x,y]/(x^n+y^n-1), its single quotient-ring relation, and the
Euler form omega = y dx - x dy (route §3.1, (A3)/(A4) input). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual

/-- Polynomial model of the two affine coordinates. -/
abbrev Poly : Type := MvPolynomial (Fin 2) ℚ
/-- The actual affine chart ring A0 = k[x,y]/(x^n+y^n-1). -/
abbrev B (n : ℕ) : Type := R n

/-- The x coordinate in the affine chart. -/
def coordX (n : ℕ) : B n := Ideal.Quotient.mk _ (MvPolynomial.X 0)
/-- The y coordinate in the affine chart. -/
def coordY (n : ℕ) : B n := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The Fermat relation x^n + y^n - 1 = 0 in the actual chart ring. -/
theorem relation (n : ℕ) : coordX n ^ n + coordY n ^ n - 1 = 0 := by
  have hmem : fermatEquation n ∈ Ideal.span ({fermatEquation n} : Set Poly) :=
    Ideal.subset_span (by simp)
  have hmk : Ideal.Quotient.mk (Ideal.span ({fermatEquation n} : Set Poly))
      (fermatEquation n) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hsub : coordX n ^ n + coordY n ^ n - 1 = 0 := by
    rw [coordX, coordY, ← map_one (Ideal.Quotient.mk _), ← map_pow, ← map_pow,
      ← map_add, ← map_sub]
    exact hmk
  exact hsub

/-- The actual absolute differential module Omega_{A0/k}. -/
abbrev Omega (n : ℕ) : Type := KaehlerDifferential ℚ (B n)
/-- dx in Omega_{A0/k}. -/
def dX (n : ℕ) : Omega n := KaehlerDifferential.D ℚ (B n) (coordX n)
/-- dy in Omega_{A0/k}. -/
def dY (n : ℕ) : Omega n := KaehlerDifferential.D ℚ (B n) (coordY n)

/-- Converts a natural-number multiple of a vector to a ring multiple. -/
theorem nsmul_smul_eq (n : ℕ) (a : B n) (z : Omega n) :
    n • (a • z) = ((n : B n) * a) • z := by
  rw [← Nat.cast_smul_eq_nsmul (B n) n, smul_smul]


/-- The single quotient-ring relation of Omega_{A0/k}:
n x^(n-1) dx + n y^(n-1) dy = 0. -/
theorem derivation_relation (n : ℕ) :
    ((n : B n) * coordX n ^ (n - 1)) • dX n + ((n : B n) * coordY n ^ (n - 1)) • dY n = 0 := by
  have h0 : KaehlerDifferential.D ℚ (B n) (coordX n ^ n) +
      KaehlerDifferential.D ℚ (B n) (coordY n ^ n) = 0 := by
    have h := congrArg (KaehlerDifferential.D ℚ (B n)) (relation n)
    simpa [map_sub, map_add, map_one, Derivation.map_one_eq_zero] using h
  have hx : KaehlerDifferential.D ℚ (B n) (coordX n ^ n) =
      n • (coordX n ^ (n - 1) • dX n) := by
    rw [Derivation.leibniz_pow, dX]
  have hy : KaehlerDifferential.D ℚ (B n) (coordY n ^ n) =
      n • (coordY n ^ (n - 1) • dY n) := by
    rw [Derivation.leibniz_pow, dY]
  rw [hx, hy] at h0
  rw [nsmul_smul_eq, nsmul_smul_eq] at h0
  exact h0

/-- The Euler form omega = y dx - x dy in Omega_{A0/k}; the route's section is
omega0 = (1/n) omega (they differ by the global scalar unit 1/n). -/
def omegaForm (n : ℕ) : Omega n :=
  coordY n • dX n - coordX n • dY n

/-- The presentation map B^2 -> Omega, (a,b) |-> a dx + b dy. -/
noncomputable def presMap (n : ℕ) : (Fin 2 →₀ B n) →ₗ[B n] Omega n :=
  Finsupp.lsum (B n) (fun i => LinearMap.toSpanSingleton (B n) (Omega n)
    (if i = 0 then dX n else dY n))

/-- The image of the single relation vector under the presentation map is zero. -/
theorem presMap_relation (n : ℕ) :
    presMap n (Finsupp.single 0 ((n : B n) * coordX n ^ (n - 1)) +
      Finsupp.single 1 ((n : B n) * coordY n ^ (n - 1))) = 0 := by
  rw [presMap, map_add, Finsupp.lsum_single, Finsupp.lsum_single]
  simp only [LinearMap.toSpanSingleton_apply, Fin.isValue, if_true]
  exact derivation_relation n

#print axioms relation
#print axioms derivation_relation
#print axioms presMap_relation
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
