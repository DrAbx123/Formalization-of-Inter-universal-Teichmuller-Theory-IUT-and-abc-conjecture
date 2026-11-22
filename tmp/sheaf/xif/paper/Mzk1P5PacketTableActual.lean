import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHullSpan
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5PacketTableActual
open LeanFormal.IUT.LocalFieldProductHull
variable {J : Type*} {E : J → Type*} [∀ j, NormedField (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
/-- The P5 four-column table: source arrow/root equation, tensor factor
coordinate, valuation, and Haar reference lattice.  The actual packet data are
explicit fields; no inhabitant is asserted here. -/
structure PacketFourColumnTable where
  sourceArrowRootEquation : Prop
  tensorFactorIndex : Type
  tensorFactorProjection : tensorFactorIndex → J
  tensorFactorValuation : tensorFactorIndex → Real
  haarReferenceLattice : Submodule (integralRing hna) ((j : J) → E j)
/-- `Γ_t` as the integral span of the actual finite source image. -/
def gammaOfSourceImage (S : Set ((j : J) → E j)) :
    Set ((j : J) → E j) :=
  (Submodule.span (integralRing hna) S : Set ((j : J) → E j))
/-- `H_t` as the actual integral holomorphic hull of the same source image. -/
def hullOfSourceImage (S : Set ((j : J) → E j)) :
    Set ((j : J) → E j) :=
  hull S
/-- P5 lower bound: the actual integral span `Γ_t` is contained in the hull
`H_t`.  This is the GREEN donor `integralSpan_subset_hull`; it needs no new
source input once `S` is the actual finite source image. -/
theorem gamma_subset_hull (S : Set ((j : J) → E j)) :
    gammaOfSourceImage hna S ⊆ hullOfSourceImage S :=
  integralSpan_subset_hull hna S
#check PacketFourColumnTable
#check gammaOfSourceImage
#check hullOfSourceImage
#check gamma_subset_hull
end LeanFormal.IUT.XiFPaper.Mzk1P5PacketTableActual
end