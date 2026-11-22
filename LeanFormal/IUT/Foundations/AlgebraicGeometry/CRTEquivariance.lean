/-
  CRT equivariance for the split-case corner decomposition.

  For x : Fin n -> S, g : G, and every global atom A, the corner reduction of
  g • x is the cornerSigma action applied to the corner reduction of x.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseCornerPermutation
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CRTEquivariance

open SplitCaseCornerPermutation

universe u

variable {S : Type u} [CommRing S] {G : Type u} [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)]

/-- Main CRT equivariance: pointwise on every atom A and coordinate j. -/
theorem crtEquivariance (x : Fin n → S) (g : G) :
    (fun (A : Finset (K G n)) (j : Fin n) =>
        Ideal.Quotient.mk (I (S := S) A) ((g • x) j)) =
      (fun (A : Finset (K G n)) (j : Fin n) =>
        cornerSigma (S := S) A g
          (fun k => Ideal.Quotient.mk (I (S := S) A) (x k)) j) := by
  funext A j
  simpa [cornerMap] using
    (congrFun (cornerSigma_cornerMap (S := S) A g x) j).symm

/-- At a nonzero atom, cornerSigma is the permutation action induced by the corner
permutation.  This is the `cornerSigma_eq_toAlgEquiv` input of the qside CRT
equivariance assembly. -/
theorem cornerSigma_apply_eq_permAction (A : Finset (K G n))
    (hA : eA (S := S) A ≠ 0) (g : G) (x : Fin n → SA (S := S) A) :
    cornerSigma (S := S) A g x =
      letI : MulAction G (Fin n) :=
        MulAction.compHom (Fin n) (cornerPermutationHom (S := S) A hA)
      letI : MulSemiringAction G (Fin n → SA (S := S) A) :=
        ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
          (R := SA (S := S) A) (G := G)
          (ρ := cornerPermutationHom (S := S) A hA)
      letI : SMulCommClass G (SA (S := S) A) (Fin n → SA (S := S) A) :=
        ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
          (R := SA (S := S) A) (G := G)
          (ρ := cornerPermutationHom (S := S) A hA)
      MulSemiringAction.toAlgEquiv (SA (S := S) A) (Fin n → SA (S := S) A) g x := by
  letI : MulAction G (Fin n) :=
    MulAction.compHom (Fin n) (cornerPermutationHom (S := S) A hA)
  letI : MulSemiringAction G (Fin n → SA (S := S) A) :=
    ABCBridge.SplitCaseCornerFixedPoints.finFunctionMulSemiringAction
      (R := SA (S := S) A) (G := G)
      (ρ := cornerPermutationHom (S := S) A hA)
  letI : SMulCommClass G (SA (S := S) A) (Fin n → SA (S := S) A) :=
    ABCBridge.SplitCaseCornerFixedPoints.finFunctionSMulCommClass
      (R := SA (S := S) A) (G := G)
      (ρ := cornerPermutationHom (S := S) A hA)
  exact congrFun
    (congrArg (fun e : ((Fin n → SA (S := S) A) ≃ₐ[SA (S := S) A]
        (Fin n → SA (S := S) A)) =>
      (e : (Fin n → SA (S := S) A) → (Fin n → SA (S := S) A)))
      (cornerSigma_eq_toAlgEquiv (S := S) A hA g)) x


end CRTEquivariance

end