import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Tactic

namespace ProbeCoprime

open LeanFormal.IUT

theorem coprime96 (l : PrimeGeFive) : Nat.Coprime 96 l.value := by
  refine Nat.Coprime.symm ?_
  rw [Nat.Prime.coprime_iff_not_dvd l.prime]
  intro hdiv
  have hdiv' : l.value ∣ 2 ^ 5 * 3 := by
    norm_num at hdiv ⊢
    exact hdiv
  have h2or3 := l.prime.dvd_mul.mp hdiv'
  rcases h2or3 with h2 | h3
  · have h2' : l.value ∣ 2 := l.prime.dvd_of_dvd_pow h2
    have hle : l.value ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    have h5 := l.ge_five
    omega
  · have hle : l.value ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    have h5 := l.ge_five
    omega

example (n : ℕ) (l : PrimeGeFive) (hdvd : n ∣ 96) : Nat.Coprime n l.value :=
  (coprime96 l).coprime_dvd_left hdvd

end ProbeCoprime
