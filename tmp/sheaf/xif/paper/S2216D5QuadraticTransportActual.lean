import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
noncomputable section
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
open Polynomial
open NumberField
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
/-- The corrected mod-29 quadratic factor is irreducible over F_29. -/
theorem s2216_quadratic_irreducible_explicit :
    Irreducible (19 + 24 * (X : (ZMod 29)[X]) + 4 * X ^ 2) := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (19 + 24 * (X : (ZMod 29)[X]) + 4 * X ^ 2).natDegree = 2 := by
      compute_degree!
    rw [hdeg]
    norm_num
  · have hnot : ∀ y : ZMod 29, 19 + 24 * y + 4 * y ^ 2 ≠ 0 := by
      decide +revert
    intro x hx
    exact hnot x (by simpa [IsRoot] using hx)
/-- The S2132 integer quadratic lift reduces to the explicit irreducible factor. -/
theorem s2216_S2132F2Z_reduction :
    S2132F2Z.map (Int.castRingHom (ZMod 29)) =
      (19 + 24 * (X : (ZMod 29)[X]) + 4 * X ^ 2) := by
  unfold S2132F2Z
  simp
/-- The S2132 corrected mod-29 quadratic factor is irreducible. -/
theorem s2216_quadratic_irreducible :
    Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29))) := by
  rw [s2216_S2132F2Z_reduction]
  exact s2216_quadratic_irreducible_explicit
/-- The residue-level inertness polynomial X^2 + X + 1 is irreducible mod 29. -/
theorem s2216_cyclotomic_three_mod29_irreducible :
    Irreducible ((X : (ZMod 29)[X]) ^ 2 + X + 1) := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X : (ZMod 29)[X]) ^ 2 + X + 1).natDegree = 2 := by compute_degree!
    rw [hdeg]
    norm_num
  · have hnot : ∀ y : ZMod 29, y ^ 2 + y + 1 ≠ 0 := by
      decide +revert
    intro x hx
    exact hnot x (by simpa [IsRoot] using hx)
/-- 29 is 2 mod 3, the residue criterion for the inert prime. -/
theorem s2216_29_mod_three : (29 : ZMod 3) = 2 := by decide
/-- The actual cyclotomic model of Q(sqrt(-3)). -/
abbrev s2216QsqrtNeg3 : Type := CyclotomicField 3 ℚ
/-- Exact missing ring-of-integers inertness: (29) is prime in O_{Q(sqrt(-3))}. -/
def s2216TwentyNineInert : Prop :=
  (Ideal.span {(29 : RingOfIntegers (s2216QsqrtNeg3))}).IsPrime
/-- The absolute 5-division field over Q. -/
abbrev s2216AbsoluteFiveDivisionField : Type :=
  Polynomial.SplittingField S2057Psi5Q
/-- Exact linear-disjointness statement for a chosen pair of embeddings into a
common algebraically closed field. -/
def s2216LinearDisjointness
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω]
    (iF : S1720Field →ₐ[ℚ] Ω)
    (iL : s2216AbsoluteFiveDivisionField →ₐ[ℚ] Ω) : Prop :=
  (IntermediateField.map iF ⊤) ⊓ (IntermediateField.map iL ⊤) = ⊥
/-- Exact missing carrier: the intersection of F' and the absolute 5-division
field is Q.  No inhabitant is asserted. -/
def s2216LinearDisjointnessRequired : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω) (_ : IsAlgClosed Ω)
    (iF : S1720Field →ₐ[ℚ] Ω)
    (iL : s2216AbsoluteFiveDivisionField →ₐ[ℚ] Ω),
    s2216LinearDisjointness Ω iF iL
#print axioms s2216_quadratic_irreducible
#print axioms s2216_cyclotomic_three_mod29_irreducible
#print axioms s2216_29_mod_three
end LeanFormal.IUT.XiFPaper.S2216D5QuadraticTransportActual
end
