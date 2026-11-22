import LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints

noncomputable section
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.ConstantRankFixedPoints

namespace LeanFormal.IUT.XiFPaper.S2529FixedPointFiniteEtaleActual

universe u

theorem S2529_fixedPointSubalgebra_finiteEtale_of_field
    {K A G : Type u} [Field K] [CommRing A] [Algebra K A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G K A]
    [Algebra.Etale K A] [Module.Finite K A] :
    Algebra.Etale K (fixedPointSubalgebra K A G) ∧
      Module.Finite K (fixedPointSubalgebra K A G) := by
  exact fixedPointSubalgebra_finiteEtale_of_local (R := K) (A := A) (G := G)

#check S2529_fixedPointSubalgebra_finiteEtale_of_field
#print axioms S2529_fixedPointSubalgebra_finiteEtale_of_field
end LeanFormal.IUT.XiFPaper.S2529FixedPointFiniteEtaleActual
end