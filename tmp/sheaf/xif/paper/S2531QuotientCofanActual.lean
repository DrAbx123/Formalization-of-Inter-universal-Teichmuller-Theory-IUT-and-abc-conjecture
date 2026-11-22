import tmp.sheaf.xif.paper.S2530CoverQuotientObjectActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

noncomputable section
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.XiFPaper.S2529FixedPointFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2530CoverQuotientObjectActual

namespace LeanFormal.IUT.XiFPaper.S2531QuotientCofanActual

universe u
variable {K A G : Type u} [Field K] [CommRing A] [Algebra K A]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G K A]
  [Algebra.Etale K A] [Module.Finite K A]

noncomputable def S2531QuotientObject : CommAlgCat.FiniteEtale K :=
  S2530InvariantObject (K := K) (A := A) (G := G)

noncomputable def S2531TargetObject : CommAlgCat.FiniteEtale K :=
  CommAlgCat.FiniteEtale.of (R := K) (S := A)

noncomputable def S2531QuotientMap :
    S2531QuotientObject (K := K) (A := A) (G := G) ⟶
      S2531TargetObject (K := K) (A := A) := by
  have h := S2529_fixedPointSubalgebra_finiteEtale_of_field
    (K := K) (A := A) (G := G)
  haveI : Algebra.Etale K (fixedPointSubalgebra K A G) := h.1
  haveI : Module.Finite K (fixedPointSubalgebra K A G) := h.2
  change CommAlgCat.FiniteEtale.of (R := K) (S := fixedPointSubalgebra K A G) ⟶
    CommAlgCat.FiniteEtale.of (R := K) (S := A)
  exact CommAlgCat.FiniteEtale.ofHom (fixedPointInclusion K A G)

theorem S2531QuotientMap_invariant (g : G)
    (x : fixedPointSubalgebra K A G) :
    groupActionRingEquiv A G g (fixedPointInclusion K A G x) =
      fixedPointInclusion K A G x :=
  fixedPointInclusion_smul (R := K) (A := A) (G := G) g x

theorem S2531QuotientUniversal
    {B : Type u} [CommRing B] [Algebra K B]
    (φ : B →ₐ[K] A)
    (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b) :
    ∃! ψ : B →ₐ[K] fixedPointSubalgebra K A G,
      (fixedPointInclusion K A G).comp ψ = φ :=
  affineFixedPointQuotient_lift_algHom (R := K) (A := A) (G := G) φ hφ

#check S2531QuotientMap
#check S2531QuotientUniversal
#print axioms S2531QuotientUniversal
end LeanFormal.IUT.XiFPaper.S2531QuotientCofanActual
end