/- G1a Fermat Riemann-Hurwitz data. -/
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRiemannHurwitzActual
structure FermatRHData where
  n : ℕ
  hn : 3 ≤ n
  genus : ℚ
rh_eq : 2 * genus - 2 = (n : ℚ) * ((n : ℚ) - 3)
noncomputable def fermatRHData (n : ℕ) (hn : 3 ≤ n) : FermatRHData where
  n := n
  hn := hn
  genus := ((n : ℚ) * ((n : ℚ) - 3)) / 2 + 1
  rh_eq := by ring
theorem fermatRHData_rh (n : ℕ) (hn : 3 ≤ n) :
    2 * (fermatRHData n hn).genus - 2 = (n : ℚ) * ((n : ℚ) - 3) := by
  exact (fermatRHData n hn).rh_eq
#print axioms fermatRHData_rh
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRiemannHurwitzActual
