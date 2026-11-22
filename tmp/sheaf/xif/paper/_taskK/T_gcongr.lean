import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option maxHeartbeats 400000

-- control: gcongr availability
example (a b : ℝ) (h : a ≤ b) : a + 1 ≤ b + 1 := by gcongr

-- G1
example (N l : ℝ) (hN : 0 ≤ N) (hl : 5 ≤ l) : N / (2*l) ≤ N := by
  gcongr

-- G2
example (N l : ℝ) (hN : 0 ≤ N) (h2 : (1:ℝ) ≤ 2*l) (hpos : 0 < 2*l) : N / (2*l) ≤ N := by
  gcongr

-- G3
example (p : ℝ) (hp : 1 < p) (a b : ℝ) (h : b ≤ a) : p^(-a) ≤ p^(-b) := by
  gcongr

-- G4
example (p : ℝ) (hp : 1 < p) (N : ℝ) (hN : 0 ≤ N) (l : ℝ) (hl : 5 ≤ l) : p^(-(N/(2*l))) ≤ p^(-(N/(4*l))) := by
  gcongr

-- G5
example (p : ℝ) (hp : 0 < p) (a b : ℝ) : p^(-(a+b)) = p^(-a) * p^(-b) := by
  gcongr

-- G6
example (k : ℕ) : (∑ i in Finset.range k, ((i:ℝ)+1)^2) = (k:ℝ)*((k:ℝ)+1)*(2*(k:ℝ)+1)/6 := by
  gcongr

-- G7
example : (1/(14:ℝ)) * (∑ i : Fin 14, ((((i.1:ℝ)+1)^2) / (2*29))) = 5/4 := by
  gcongr

-- G8
example (i l : ℕ) (h : i < (l-1)/2) (h5 : 5 ≤ l) : i + 1 ≤ (l-1)/2 := by
  gcongr

-- G9
example (j : ℤ) (hj : 1 ≤ j) : (1:ℤ) ≤ j^2 := by
  gcongr

-- G10
example (p : ℕ) [Fact (Nat.Prime p)] : (1:ℝ) < (p:ℝ) := by
  gcongr

-- G11
example (N l : ℝ) (hl : l ≠ 0) : (N / (2*l)) * (2*l) = N := by
  gcongr

-- G12
example (N l : ℝ) (hl : l ≠ 0) : N / (2*l) = N/2/l := by
  gcongr

-- G13
example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : Real.log a ≤ Real.log b := by
  gcongr

-- G14
example (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : Real.log x ≤ 0 := by
  gcongr

-- G15
example (x : ℝ) : 0 < x^2 + 1 := by
  gcongr

-- G16
example (p : ℝ) (hp : 0 < p) (a : ℝ) : 0 < p^(-a) := by
  gcongr

-- G17
example (k : ℕ) (hk : 0 < k) : (∑ _ : Fin k, ((k:ℝ)⁻¹)) = 1 := by
  gcongr

-- G18
example (N : ℝ) (hN : 0 ≤ N) (l : ℝ) (hl : 1 ≤ l) : N / (2*l) ≤ N/2 := by
  gcongr

-- G19
example (x : ℝ) (hx : 0 ≤ x) : x / (x + 1) ≤ 1 := by
  gcongr

-- G20
example (a b : ℝ) : a ≤ |a| + |b| := by
  gcongr

-- END gcongr
