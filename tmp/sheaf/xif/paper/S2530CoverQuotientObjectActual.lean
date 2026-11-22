import tmp.sheaf.xif.paper.S2529FixedPointFiniteEtaleActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

noncomputable section
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.XiFPaper.S2529FixedPointFiniteEtaleActual

namespace LeanFormal.IUT.XiFPaper.S2530CoverQuotientObjectActual

universe u

variable {K A G : Type u} [Field K] [CommRing A] [Algebra K A]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G K A]
  [Algebra.Etale K A] [Module.Finite K A]

noncomputable def S2530InvariantObject : CommAlgCat.FiniteEtale K := by
  have h := S2529_fixedPointSubalgebra_finiteEtale_of_field
    (K := K) (A := A) (G := G)
  haveI : Algebra.Etale K (fixedPointSubalgebra K A G) := h.1
  haveI : Module.Finite K (fixedPointSubalgebra K A G) := h.2
  exact CommAlgCat.FiniteEtale.of (R := K) (S := fixedPointSubalgebra K A G)

noncomputable def S2530Inclusion
    (K A G : Type u) [CommRing K] [CommRing A] [Algebra K A]
    [Group G] [MulSemiringAction G A] [SMulCommClass G K A] :
    fixedPointSubalgebra K A G →ₐ[K] A :=
  fixedPointInclusion K A G

#check S2530InvariantObject
#check S2530Inclusion
#print axioms S2530InvariantObject
end LeanFormal.IUT.XiFPaper.S2530CoverQuotientObjectActual
end