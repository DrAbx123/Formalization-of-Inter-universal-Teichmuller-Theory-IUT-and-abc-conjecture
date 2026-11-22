import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1734AffineModelDataActual

/-- The base-change model of every actual finite-etale cover is affine: it is
finite over the affine base `Spec R'`. -/
theorem S1734Model_isAffine (A : S1728Cover) :
    IsAffine (S1733Model A).left := by
  haveI : IsAffine (S1726AffineOver).left := by
    change IsAffine (Spec (CommRingCat.of S1726CoordinateRing))
    infer_instance
  haveI : IsFinite (S1733ModelOver A).left := (S1733Model_finiteEtale A).1
  exact isAffine_of_isAffineHom (S1733ModelOver A).left

/-- The affine model data without the hom equivalence: model, structure map,
affineness, finiteness and etaleness are all actual. -/
structure S1734AffineCoverModelData where
  model : S1728Cover -> Iut.SchemeOverField S1726K
  toBase : forall A, model A ⟶ S1726AffineOver
  isAffine : forall A, IsAffine (model A).left
  isFinite : forall A, IsFinite (toBase A).left
  isEtale : forall A, Etale (toBase A).left

/-- Actual inhabitant: use the base-change model of every cover. -/
noncomputable def S1734AffineCoverModelDataActual :
    S1734AffineCoverModelData where
  model := S1733Model
  toBase := S1733ModelOver
  isAffine := S1734Model_isAffine
  isFinite := fun A => (S1733Model_finiteEtale A).1
  isEtale := fun A => (S1733Model_finiteEtale A).2

/-- The exact remaining field of `S1733AffineCoverModel`: a bijection
between model morphisms and actual cover maps.  It is not supplied by the
base-change presentation. -/
def S1734HomEquivMissing : Prop :=
  forall A B : S1728Cover,
    Nonempty ((S1733Model A ⟶ S1733Model B) ≃ S1728CoverMap A B)

#print axioms S1734Model_isAffine
#print axioms S1734AffineCoverModelDataActual

end LeanFormal.IUT.XiFPaper.S1734AffineModelDataActual
end
