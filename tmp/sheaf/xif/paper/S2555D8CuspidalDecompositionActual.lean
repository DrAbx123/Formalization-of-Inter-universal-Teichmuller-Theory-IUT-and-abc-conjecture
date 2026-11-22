import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.XiFPaper.S2555D8CuspidalDecompositionActual

universe u
variable {F : Type u} [Field F]
variable {X : Iut.HyperbolicOrbicurve F}
variable {galois : ProfiniteGrp.{u}}
variable (groups : Iut.OrbicurveFundamentalGroupData X galois)
variable (cusp : Iut.OrbicurveBoundaryCusp X)

noncomputable def S2555CuspidalDecomposition :
    Iut.OrbicurveCuspidalDecompositionData groups where
  cusp := cusp
  decompositionSubgroup :=
    { toSubgroup := ⊤
      isClosed' := by
        show IsClosed (Set.univ)
        exact isClosed_univ }
  decompositionProjection_surjective := by
    intro y
    obtain ⟨x, hx⟩ := groups.projection_surjective y
    refine ⟨(⟨x, trivial⟩ : (⊤ : Subgroup groups.arithmetic.group)), ?_⟩
    change groups.projection x = y
    exact hx

theorem S2555CuspidalDecomposition_cusp
    (groups : Iut.OrbicurveFundamentalGroupData X galois)
    (cusp : Iut.OrbicurveBoundaryCusp X) :
    (S2555CuspidalDecomposition groups cusp).cusp = cusp :=
  rfl

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S} {B : SourceClauseB A S C}
variable {D : SourceClauseC A S C B} {E : SourceClauseD A S C B D}
variable {L : SourceClauseE A S C B D E}

noncomputable def S2555SourceClauseF
    (O : TorsionQuotientBoundaryOrigin l A S.cK)
    (hbasis : O.rank_one_quotient.torsion_basis = D.k_torsion_basis)
    (hcuspeq : O.cusp = S.epsilon) :
    SourceClauseF A S C B D E L where
  boundary_origin := O
  quotient_basis_eq_k_torsion_basis := hbasis
  boundary_cusp_eq_epsilon := hcuspeq
  cusp_decomposition :=
    S2555CuspidalDecomposition E.c_groups.groups O.cusp
  cusp_decomposition_cusp_eq_origin := rfl

#check S2555SourceClauseF
#print axioms S2555SourceClauseF
#check S2555CuspidalDecomposition
#print axioms S2555CuspidalDecomposition
end LeanFormal.IUT.XiFPaper.S2555D8CuspidalDecompositionActual
end