import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.Algebra.Algebra.Pi

/-!
# The coordinate hull respects a grouping into blocks

A common admissible nonzero dilation lets every candidate bound on one block
extend to a global candidate. Hence the actual global hull becomes the product
of the projected hulls. The boundedness hypothesis matters: the unbounded
whole-ambient branch need not satisfy this identity.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

noncomputable section

variable {B : Type*} {J : B → Type*} {K : Sigma J → Type*} [∀ w, NormedField (K w)]

def blockProjection (b : B) (x : (w : Sigma J) → K w) : (j : J b) → K ⟨b, j⟩ :=
  fun j => x ⟨b, j⟩

def blockCoordinatesHomeomorph :
    ((w : Sigma J) → K w) ≃ₜ ((b : B) → (j : J b) → K ⟨b, j⟩) where
  toFun x b j := x ⟨b, j⟩
  invFun y w := y w.1 w.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi
    (fun b => continuous_pi (fun j => continuous_apply (⟨b, j⟩ : Sigma J)))
  continuous_invFun := continuous_pi (fun w => (continuous_apply w.2).comp (continuous_apply w.1))

def blockCoordinatesAlgEquiv (R : Type*) [CommSemiring R] [∀ w, Algebra R (K w)] :
    ((w : Sigma J) → K w) ≃ₐ[R] ((b : B) → (j : J b) → K ⟨b, j⟩) where
  toEquiv := blockCoordinatesHomeomorph.toEquiv
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem mem_hull_iff_blocks_of_bound {S : Set ((w : Sigma J) → K w)}
    (bound : (w : Sigma J) → K w) (hbound : ∀ w, bound w ≠ 0) (hS : S ⊆ region bound)
    (x : (w : Sigma J) → K w) :
    x ∈ hull S ↔ ∀ b, blockProjection b x ∈ hull (blockProjection b '' S) := by
  classical
  constructor
  · intro hx b lam hlam hlocal
    let combined : (b : B) → (j : J b) → K ⟨b, j⟩ :=
      Function.update (fun b j => bound ⟨b, j⟩) b lam
    let globalBound : (w : Sigma J) → K w := fun w => combined w.1 w.2
    have hglobal : ∀ w, globalBound w ≠ 0 := by
      rintro ⟨c, j⟩
      by_cases hc : c = b
      · subst c
        simpa [globalBound, combined, Function.update] using hlam j
      · simpa [globalBound, combined, Function.update, hc] using hbound ⟨c, j⟩
    have hglobalS : S ⊆ region globalBound := by
      intro y hy w
      rcases w with ⟨c, j⟩
      by_cases hc : c = b
      · subst c
        simpa [globalBound, combined, Function.update, blockProjection] using
          hlocal ⟨y, hy, rfl⟩ j
      · simpa [globalBound, combined, Function.update, hc] using hS hy ⟨c, j⟩
    intro j
    simpa [globalBound, combined, Function.update, blockProjection] using
      hx globalBound hglobal hglobalS ⟨b, j⟩
  · intro hx lam hlam hglobal w
    rcases w with ⟨b, j⟩
    exact hx b (fun j => lam ⟨b, j⟩) (fun j => hlam ⟨b, j⟩)
      (by rintro _ ⟨y, hy, rfl⟩ k; exact hglobal hy ⟨b, k⟩) j

theorem blockCoordinatesHomeomorph_image_hull_of_bound {S : Set ((w : Sigma J) → K w)}
    (bound : (w : Sigma J) → K w) (hbound : ∀ w, bound w ≠ 0) (hS : S ⊆ region bound) :
    blockCoordinatesHomeomorph '' hull S =
      Set.pi Set.univ (fun b => hull (blockProjection b '' S)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ b _
    exact (mem_hull_iff_blocks_of_bound bound hbound hS x).mp hx b
  · intro hy
    refine ⟨blockCoordinatesHomeomorph.symm y, ?_, blockCoordinatesHomeomorph.apply_symm_apply y⟩
    exact (mem_hull_iff_blocks_of_bound bound hbound hS _).mpr
      (fun b => hy b (Set.mem_univ _))

theorem blockCoordinatesHomeomorph_image_hull {S : Set ((w : Sigma J) → K w)}
    (hS : IsCompact S) (hne : S.Nonempty) (hcoord : ∀ w, ∃ x ∈ S, x w ≠ 0) :
    blockCoordinatesHomeomorph '' hull S =
      Set.pi Set.univ (fun b => hull (blockProjection b '' S)) := by
  obtain ⟨bound, hbound, hsub, _⟩ := exists_least_region hS hne hcoord
  exact blockCoordinatesHomeomorph_image_hull_of_bound bound hbound hsub

end

end LeanFormal.IUT.LocalFieldProductHull
