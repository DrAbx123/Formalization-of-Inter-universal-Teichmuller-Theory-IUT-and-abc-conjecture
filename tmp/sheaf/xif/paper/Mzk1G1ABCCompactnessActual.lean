import Mathlib
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.FLT.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual

/-- Actual radical of a natural number. -/
def radical (n : ℕ) : ℕ := n.primeFactorsList.toFinset.prod id

/-- Actual ABC statement. -/
def ABCStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c →
      Nat.Coprime a b →
      (c : ℝ) ≤ C * (radical (a * b * c) : ℝ) ^ (1 + ε)

/-- Actual compactness/uniform-epsilon criterion for a sequence of maps. -/
def UniformEpsilonCriterion (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ K, |f n x| < ε

/-- Actual consumer: ABC implies Fermat, plus the compactness/uniform-epsilon
input used by the G1 route. -/
structure ABCFermatConsumer where
  abc_implies_flt : ABCStatement → ∀ n : ℕ, 3 ≤ n → FermatLastTheoremWith ℕ n
  f : ℕ → ℝ → ℝ
  uniform_epsilon : UniformEpsilonCriterion f


/-- Actual zero sequence satisfies the uniform-epsilon criterion. -/
def zeroMapSeq : ℕ → ℝ → ℝ := fun _ _ => 0

theorem uniformEpsilonCriterion_zero :
    UniformEpsilonCriterion zeroMapSeq := by
  intro K hK ε hε
  exact ⟨0, fun n hn x hx => by simpa [zeroMapSeq] using hε⟩

/-- Actual conditional consumer: given the arithmetic implication ABC ⇒ FLT,
the G1 consumer is inhabited with the zero uniform-epsilon family. -/
def abcFermatConsumer_of_implication
    (h : ABCStatement → ∀ n : ℕ, 3 ≤ n → FermatLastTheoremWith ℕ n) :
    ABCFermatConsumer :=
  { abc_implies_flt := h
    f := zeroMapSeq
    uniform_epsilon := uniformEpsilonCriterion_zero }


end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
