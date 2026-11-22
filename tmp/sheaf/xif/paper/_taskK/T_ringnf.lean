import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option maxHeartbeats 400000

-- control: ringnf availability
example (x y : ℝ) : (x+y)^2 = x^2 + 2*x*y + y^2 := by ring

-- G1
example (N l : ℝ) (hN : 0 ≤ N) (hl : 5 ≤ l) : N / (2*l) ≤ N := by
  ring_nf

-- G2
example (N l : ℝ) (hN : 0 ≤ N) (h2 : (1:ℝ) ≤ 2*l) (hpos : 0 < 2*l) : N / (2*l) ≤ N := by
  ring_nf

-- G3
example (p : ℝ) (hp : 1 < p) (a b : ℝ) (h : b ≤ a) : p^(-a) ≤ p^(-b) := by
  ring_nf

-- G4
example (p : ℝ) (hp : 1 < p) (N : ℝ) (hN : 0 ≤ N) (l : ℝ) (hl : 5 ≤ l) : p^(-(N/(2*l))) ≤ p^(-(N/(4*l))) := by
  ring_nf

-- G5
example (p : ℝ) (hp : 0 < p) (a b : ℝ) : p^(-(a+b)) = p^(-a) * p^(-b) := by
  ring_nf

-- G6
example (k : ℕ) : (∑ i in Finset.range k, ((i:ℝ)+1)^2) = (k:ℝ)*((k:ℝ)+1)*(2*(k:ℝ)+1)/6 := by
  ring_nf

-- G7
example : (1/(14:ℝ)) * (∑ i : Fin 14, ((((i.1:ℝ)+1)^2) / (2*29))) = 5/4 := by
  ring_nf

-- G8
example (i l : ℕ) (h : i < (l-1)/2) (h5 : 5 ≤ l) : i + 1 ≤ (l-1)/2 := by
  ring_nf

-- G9
example (j : ℤ) (hj : 1 ≤ j) : (1:ℤ) ≤ j^2 := by
  ring_nf

-- G10
example (p : ℕ) [Fact (Nat.Prime p)] : (1:ℝ) < (p:ℝ) := by
  ring_nf

-- G11
example (N l : ℝ) (hl : l ≠ 0) : (N / (2*l)) * (2*l) = N := by
  ring_nf

-- G12
example (N l : ℝ) (hl : l ≠ 0) : N / (2*l) = N/2/l := by
  ring_nf

-- G13
example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : Real.log a ≤ Real.log b := by
  ring_nf

-- G14
example (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : Real.log x ≤ 0 := by
  ring_nf

-- G15
example (x : ℝ) : 0 < x^2 + 1 := by
  ring_nf

-- G16
example (p : ℝ) (hp : 0 < p) (a : ℝ) : 0 < p^(-a) := by
  ring_nf

-- G17
example (k : ℕ) (hk : 0 < k) : (∑ _ : Fin k, ((k:ℝ)⁻¹)) = 1 := by
  ring_nf

-- G18
example (N : ℝ) (hN : 0 ≤ N) (l : ℝ) (hl : 1 ≤ l) : N / (2*l) ≤ N/2 := by
  ring_nf

-- G19
example (x : ℝ) (hx : 0 ≤ x) : x / (x + 1) ≤ 1 := by
  ring_nf

-- G20
example (a b : ℝ) : a ≤ |a| + |b| := by
  ring_nf

-- END ringnf
