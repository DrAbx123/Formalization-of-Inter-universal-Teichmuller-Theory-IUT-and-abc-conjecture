import tmp.sheaf.xif.paper.Mzk1P5PacketTableActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
open LeanFormal.IUT.LocalFieldProductHull
variable {J : Type*} {E : J → Type*} [∀ j, NormedField (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
/-- P5 gamma is the integral span of a source image. -/
def gammaP5 (S : Set ((j : J) → E j)) : Set ((j : J) → E j) :=
  (Submodule.span (integralRing hna) S : Set ((j : J) → E j))
/-- P5 H_t is the actual integral holomorphic hull. -/
def HP5 (S : Set ((j : J) → E j)) : Set ((j : J) → E j) := hull S
/-- GREEN: Γ_t ⊆ H_t from the donor `integralSpan_subset_hull`. -/
theorem gammaP5_subset_HP5 (S : Set ((j : J) → E j)) :
    gammaP5 hna S ⊆ HP5 S := integralSpan_subset_hull hna S
#check gammaP5_subset_HP5
end LeanFormal.IUT.XiFPaper.Mzk1P5GammaSubsetHullActual
end