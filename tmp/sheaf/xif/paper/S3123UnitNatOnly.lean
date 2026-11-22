import tmp.sheaf.xif.paper.S3123UnitHomActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123UnitActual
open LeanFormal.IUT.XiFPaper.S3123UnitHomActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitNatOnly

variable {l : PrimeGeFive}

noncomputable def S3123E
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    ((Over.map (S3123BaseSpecMap (l := l))).obj (Opposite.unop U.as) ⟶
      S1419AffineOver (l := l)) ≃
      (Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :=
  (Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
    (Opposite.unop U.as) (S1419AffineOver (l := l))

set_option maxHeartbeats 2000000 in
lemma S3123UnitNat
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    {X Y : (S3123Left (l := l)).obj U} (f : X ⟶ Y) :
    (𝟭 ((S3123Left (l := l)).obj U)).map f ≫
        Discrete.eqToHom (by
          change Y.as = S3123E (l := l) U ((S3123E (l := l) U).symm Y.as)
          exact (Equiv.apply_symm_apply _ _).symm) =
      Discrete.eqToHom (by
          change X.as = S3123E (l := l) U ((S3123E (l := l) U).symm X.as)
          exact (Equiv.apply_symm_apply _ _).symm) ≫
        ((S3123FiberApp (l := l) U ≫ S3123FiberAppInv (l := l) U).toFunctor.map f) := by
  rcases X with ⟨x⟩
  rcases Y with ⟨y⟩
  conv_rhs =>
    rw [CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj]
  simp only [Functor.id_obj, Functor.id_map, S3123FiberApp_apply,
    S3123FiberAppInv_apply]
  haveI : Subsingleton ((Discrete.mk x) ⟶
      (Discrete.mk (S3123E (l := l) U ((S3123E (l := l) U).symm y)))) :=
    S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  exact Subsingleton.elim _ _

#check S3123UnitNat

end LeanFormal.IUT.XiFPaper.S3123UnitNatOnly
end
