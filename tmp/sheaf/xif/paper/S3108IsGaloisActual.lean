import Mathlib
import tmp.sheaf.xif.paper.S3108X2SeparableActual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S3108X2SeparableActual

namespace LeanFormal.IUT.XiFPaper.S3108IsGaloisActual

/-- The Gaussian polynomial `X^2 + 1` over `ℚ`. -/
def p : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (-1)

/-- The actual splitting field `F = ℚ(i)` as `AdjoinRoot p`. -/
abbrev F : Type := AdjoinRoot p

/-- The actual root `i` in `F`. -/
def root : F := AdjoinRoot.root p

local instance : Fact (Irreducible p) :=
  ⟨by
    rw [show p = (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ) by rfl]
    exact X_pow_sub_C_irreducible_of_prime (p := 2) (by norm_num) (a := (-1 : ℚ))
      (by
        intro b hb
        nlinarith [sq_nonneg b])⟩

theorem S3108_root_sq : root ^ 2 = -1 := by
  change AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (-1)) ^ 2 = -1
  have h := AdjoinRoot.eval₂_root p
  simp [p] at h
  exact eq_neg_of_add_eq_zero_left h

theorem S3108_adjoin_rootSet_eq_top (hroot : root ^ 2 = -1) :
    Algebra.adjoin ℚ (p.rootSet F) = ⊤ := by
  have hpmonic : p.Monic := by
    simpa [p] using Polynomial.monic_X_pow_sub_C (-1 : ℚ) (n := 2) (by norm_num)
  have hmem : root ∈ p.rootSet F := by
    rw [Polynomial.Monic.mem_rootSet hpmonic]
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root p
  have hle : Algebra.adjoin ℚ ({root} : Set F) ≤
      Algebra.adjoin ℚ (p.rootSet F) := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Algebra.subset_adjoin hmem
  rw [eq_top_iff]
  calc
    ⊤ = Algebra.adjoin ℚ ({root} : Set F) :=
      (AdjoinRoot.adjoinRoot_eq_top (f := p)).symm
    _ ≤ Algebra.adjoin ℚ (p.rootSet F) := hle

instance : Polynomial.IsSplittingField ℚ F p := by
  refine ⟨?_, ?_⟩
  · have hmap : p.map (algebraMap ℚ F) =
        (Polynomial.X - Polynomial.C root) * (Polynomial.X + Polynomial.C root) := by
      simp only [p, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X]
      have h1 : (algebraMap ℚ F) (-1) = root ^ 2 := by
        rw [S3108_root_sq]
        simp
      rw [h1, Polynomial.C_pow]
      ring
    rw [hmap]
    have h2 : Splits ((Polynomial.X + Polynomial.C root : Polynomial F)) := by
      simpa [map_neg] using (Splits.X_sub_C (-root))
    exact (Splits.X_sub_C root).mul h2
  · exact S3108_adjoin_rootSet_eq_top S3108_root_sq

theorem S3108_isGalois : IsGalois ℚ F :=
  IsGalois.of_separable_splitting_field (p := p)
    (by simpa [p] using S3108_X2_separable)

#check S3108_isGalois
#print axioms S3108_isGalois

end LeanFormal.IUT.XiFPaper.S3108IsGaloisActual
end
