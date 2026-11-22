import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo
import tmp.sheaf.xif.paper.S2858AlphaSquareActual
import tmp.sheaf.xif.paper.S2853E37NegationAutomorphismActual
import tmp.sheaf.xif.paper.S2858AlphaOverActual
import tmp.sheaf.xif.paper.S2856HfOverlapActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaSquareActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _


/-- The chart-Z negation as a ring equivalence, using the actual involution. -/
noncomputable def S2853RingHomEquiv :
    S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃+*
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K where
  toFun := S2853RingHom S2844D6F6BaseChangeActual.K
  invFun := S2853RingHom S2844D6F6BaseChangeActual.K
  left_inv x := by
    have h := congrArg
      (fun f : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K →+*
        S2801E37CoordinateRing S2844D6F6BaseChangeActual.K => f x)
      (S2853RingHom_comp_self S2844D6F6BaseChangeActual.K)
    simpa [RingHom.comp_apply] using h
  right_inv x := by
    have h := congrArg
      (fun f : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K →+*
        S2801E37CoordinateRing S2844D6F6BaseChangeActual.K => f x)
      (S2853RingHom_comp_self S2844D6F6BaseChangeActual.K)
    simpa [RingHom.comp_apply] using h
  map_mul' := (S2853RingHom S2844D6F6BaseChangeActual.K).map_mul
  map_add' := (S2853RingHom S2844D6F6BaseChangeActual.K).map_add

/-- The same equivalence as a K-algebra equivalence. -/
noncomputable def S2853RingHomAlgEquiv :
    S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K :=
  AlgEquiv.ofRingEquiv (f := S2853RingHomEquiv)
    (fun r => by
      change S2853RingHom S2844D6F6BaseChangeActual.K
        (algebraMap S2844D6F6BaseChangeActual.K
          (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K) r) =
        algebraMap S2844D6F6BaseChangeActual.K
          (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K) r
      exact S2853RingHom_algebraMap S2844D6F6BaseChangeActual.K r)

/-- Exact affine order-two statement. -/
def S2889AffineOrderTwoClassification : Prop :=
  ∀ φ : S2801E37CoordinateRing S2844D6F6BaseChangeActual.K ≃ₐ[S2844D6F6BaseChangeActual.K]
      S2801E37CoordinateRing S2844D6F6BaseChangeActual.K,
    φ.toRingHom.comp φ.toRingHom =
        RingHom.id (S2801E37CoordinateRing S2844D6F6BaseChangeActual.K) →
      φ = 1 ∨ φ = S2853RingHomAlgEquiv

/-- A chart-Z preservation interface: beta's underlying scheme endomorphism
restricted to chart Z factors through chart Z. -/
def S2889ChartZPreservation
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X) : Prop :=
  ∃ z : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
      S2801E37AffineScheme S2844D6F6BaseChangeActual.K,
    z ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left

/-- Uniqueness of the chart-Z factor, using that the chart map is mono. -/
theorem S2889ChartZPreservation_unique
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    {z₁ z₂ : S2801E37AffineScheme S2844D6F6BaseChangeActual.K ⟶
      S2801E37AffineScheme S2844D6F6BaseChangeActual.K}
    (h₁ : z₁ ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left)
    (h₂ : z₂ ≫ S2820E37ChartZMap S2844D6F6BaseChangeActual.K =
      S2820E37ChartZMap S2844D6F6BaseChangeActual.K ≫ β.left) :
    z₁ = z₂ := by
  haveI : IsOpenImmersion (S2820E37ChartZMap S2844D6F6BaseChangeActual.K) :=
    (E37ProjGlueData S2844D6F6BaseChangeActual.K
      (S2820E37TransitionIso S2844D6F6BaseChangeActual.K)).ι_isOpenImmersion
      (ULift.up false)
  haveI : Mono (S2820E37ChartZMap S2844D6F6BaseChangeActual.K) :=
    IsOpenImmersion.mono _
  apply (cancel_mono (S2820E37ChartZMap S2844D6F6BaseChangeActual.K)).mp
  rw [h₁, h₂]

#check S2853RingHomEquiv
#check S2853RingHomAlgEquiv
#check S2889AffineOrderTwoClassification
#check S2889ChartZPreservation
#check S2889ChartZPreservation_unique
#print axioms S2853RingHomEquiv
#print axioms S2889ChartZPreservation_unique

end LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
end
