import tmp.sheaf.xif.paper.S2701GaussianPrimeIdealsActual

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual

namespace LeanFormal.IUT.XiFPaper.S2709IdealFactorizationActual

local instance s2709GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2709_field_factorization :
    Ideal.span {(2161 : GaussianO)} =
      gaussianField2161Plus * gaussianField2161Minus := by
  rw [gaussianField2161Plus_eq_map, gaussianField2161Minus_eq_map,
    ← Ideal.map_mul, ← gaussianInt2161_ideal_factorization]
  rw [Ideal.map_span, Set.image_singleton]
  congr 1
  rw [show (2161 : GaussianInt) = ((2161 : ℤ) : GaussianInt) by norm_num]
  rw [map_intCast]
  norm_num

theorem S2709_prime_dvd_factor
    (P : Ideal GaussianO) [hP : P.IsPrime]
    (hdiv : P ∣ gaussianField2161Plus * gaussianField2161Minus) :
    P = gaussianField2161Plus ∨ P = gaussianField2161Minus := by
  have hle : gaussianField2161Plus * gaussianField2161Minus ≤ P :=
    (Ideal.dvd_iff_le).mp hdiv
  rcases (hP.mul_le).mp hle with hplus | hminus
  · left
    exact (Ideal.IsMaximal.eq_of_le gaussianField2161Plus_isMaximal hP.ne_top hplus).symm
  · right
    exact (Ideal.IsMaximal.eq_of_le gaussianField2161Minus_isMaximal hP.ne_top hminus).symm

theorem S2709_prime_dvd_2161
    (P : Ideal GaussianO) [hP : P.IsPrime]
    (hdiv : P ∣ Ideal.span {(2161 : GaussianO)}) :
    P = gaussianField2161Plus ∨ P = gaussianField2161Minus := by
  rw [S2709_field_factorization] at hdiv
  exact S2709_prime_dvd_factor P hdiv

#check S2709_field_factorization
#check S2709_prime_dvd_factor
#check S2709_prime_dvd_2161
#print axioms S2709_field_factorization
#print axioms S2709_prime_dvd_factor
#print axioms S2709_prime_dvd_2161

end LeanFormal.IUT.XiFPaper.S2709IdealFactorizationActual
end
