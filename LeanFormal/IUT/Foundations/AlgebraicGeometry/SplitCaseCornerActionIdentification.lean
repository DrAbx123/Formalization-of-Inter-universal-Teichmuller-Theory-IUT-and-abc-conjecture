import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseCornerPermutation
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseCornerFixedPoints
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Identification of the corner action with the permutation action

Production `SplitCaseCornerPermutation.cornerSigma A g` is an `SA A`-algebra
automorphism of `(Fin n → SA A)`.  This file identifies it with the coordinate
permutation action induced by `cornerPermutationHom A hA`, which is the action
used by `SplitCaseCornerFixedPoints.cornerFixedPointsEquivFin`.
-/
namespace ABCBridge.SplitCaseCornerActionIdentification

universe u

open SplitCaseCornerPermutation
open ABCBridge.SplitCaseCornerFixedPoints

variable {S : Type u} [CommRing S] {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)]

abbrev cornerRing (A : Finset (SplitCaseCornerPermutation.K G n)) : Type u :=
  SplitCaseCornerPermutation.SA (S := S) A

abbrev cornerPerm (A : Finset (SplitCaseCornerPermutation.K G n))
    (hA : SplitCaseCornerPermutation.eA (S := S) A ≠ 0) :
    G →* Equiv.Perm (Fin n) :=
  SplitCaseCornerPermutation.cornerPermutationHom (S := S) (G := G) (n := n) A hA

theorem function_eq_sum_smul_single (f : Fin n → cornerRing (S := S) (G := G) (n := n) A) :
    f = ∑ i : Fin n, f i • (Pi.single i (1 : cornerRing (S := S) (G := G) (n := n) A)) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem algEquiv_eq_of_single (A : Finset (SplitCaseCornerPermutation.K G n))
    {φ ψ : (Fin n → cornerRing (S := S) (G := G) (n := n) A) ≃ₐ[cornerRing (S := S) (G := G) (n := n) A]
      (Fin n → cornerRing (S := S) (G := G) (n := n) A)}
    (h : ∀ i : Fin n, φ (Pi.single i (1 : cornerRing (S := S) (G := G) (n := n) A)) =
      ψ (Pi.single i (1 : cornerRing (S := S) (G := G) (n := n) A))) : φ = ψ := by
  apply AlgEquiv.ext
  intro f
  conv_lhs => rw [function_eq_sum_smul_single (S := S) (G := G) (n := n) (A := A) f]
  conv_rhs => rw [function_eq_sum_smul_single (S := S) (G := G) (n := n) (A := A) f]
  simp only [map_sum, map_smul, h]

/-- The permutation action on the corner, as a bundled algebra equivalence. -/
noncomputable def cornerPermAction (A : Finset (SplitCaseCornerPermutation.K G n))
    (hA : SplitCaseCornerPermutation.eA (S := S) A ≠ 0) (g : G) :
    (Fin n → cornerRing (S := S) (G := G) (n := n) A) ≃ₐ[cornerRing (S := S) (G := G) (n := n) A]
      (Fin n → cornerRing (S := S) (G := G) (n := n) A) := by
  letI : MulSemiringAction G (Fin n → cornerRing (S := S) (G := G) (n := n) A) :=
    finFunctionMulSemiringAction (R := cornerRing (S := S) (G := G) (n := n) A) (G := G)
      (ρ := cornerPerm (S := S) (G := G) (n := n) A hA)
  letI : SMulCommClass G (cornerRing (S := S) (G := G) (n := n) A)
      (Fin n → cornerRing (S := S) (G := G) (n := n) A) :=
    finFunctionSMulCommClass (R := cornerRing (S := S) (G := G) (n := n) A) (G := G)
      (ρ := cornerPerm (S := S) (G := G) (n := n) A hA)
  exact MulSemiringAction.toAlgEquiv (cornerRing (S := S) (G := G) (n := n) A)
    (Fin n → cornerRing (S := S) (G := G) (n := n) A) g

theorem cornerPermAction_single (A : Finset (SplitCaseCornerPermutation.K G n))
    (hA : SplitCaseCornerPermutation.eA (S := S) A ≠ 0) (g : G) (i : Fin n) :
    cornerPermAction (S := S) (G := G) (n := n) A hA g
        ((Pi.single i (1 : cornerRing (S := S) (G := G) (n := n) A) :
      Fin n → cornerRing (S := S) (G := G) (n := n) A)) =
      Pi.single (cornerPerm (S := S) (G := G) (n := n) A hA g i)
        (1 : cornerRing (S := S) (G := G) (n := n) A) := by
  letI : MulSemiringAction G (Fin n → cornerRing (S := S) (G := G) (n := n) A) :=
    finFunctionMulSemiringAction (R := cornerRing (S := S) (G := G) (n := n) A) (G := G)
      (ρ := cornerPerm (S := S) (G := G) (n := n) A hA)
  change (fun j => ((Pi.single i (1 : cornerRing (S := S) (G := G) (n := n) A) :
      Fin n → cornerRing (S := S) (G := G) (n := n) A))
      ((cornerPerm (S := S) (G := G) (n := n) A hA g)⁻¹ j)) = _
  ext j
  by_cases hj : j = cornerPerm (S := S) (G := G) (n := n) A hA g i
  · subst hj
    simp [Pi.single, Equiv.apply_symm_apply]
  · have hne : (cornerPerm (S := S) (G := G) (n := n) A hA g)⁻¹ j ≠ i := by
      intro h
      apply hj
      calc j = cornerPerm (S := S) (G := G) (n := n) A hA g
            ((cornerPerm (S := S) (G := G) (n := n) A hA g)⁻¹ j) := by simp
        _ = cornerPerm (S := S) (G := G) (n := n) A hA g i := by rw [h]
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hj]

/-- The main identification: production `cornerSigma` is the permutation action. -/
theorem cornerSigma_eq_cornerPermAction (A : Finset (SplitCaseCornerPermutation.K G n))
    (hA : SplitCaseCornerPermutation.eA (S := S) A ≠ 0) (g : G) :
    SplitCaseCornerPermutation.cornerSigma (S := S) A g =
      cornerPermAction (S := S) (G := G) (n := n) A hA g :=
  algEquiv_eq_of_single (S := S) (G := G) (n := n) A
    (φ := SplitCaseCornerPermutation.cornerSigma (S := S) A g)
    (ψ := cornerPermAction (S := S) (G := G) (n := n) A hA g)
    (by
      intro i
      rw [SplitCaseCornerPermutation.cornerPermutation_spec (S := S) A hA g i]
      exact (cornerPermAction_single (S := S) (G := G) (n := n) A hA g i).symm)

end ABCBridge.SplitCaseCornerActionIdentification