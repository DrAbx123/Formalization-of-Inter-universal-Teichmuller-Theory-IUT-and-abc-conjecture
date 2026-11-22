import tmp.sheaf.xif.paper.S3076QPrimePseudofunctorActual
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Iso
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3076QPrimePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K

lemma S3076MapIdArrow (U : LocallyDiscrete Cᵒᵖ) :
    ((𝟙 U : Discrete (U.as ⟶ U.as))).as = 𝟙 U.as :=
  rfl

lemma S3076MapIdArrowUnop (U : LocallyDiscrete Cᵒᵖ) :
    (((𝟙 U : Discrete (U.as ⟶ U.as))).as).unop = 𝟙 U.as.unop :=
  rfl

noncomputable def S3076MapIdObj (U : LocallyDiscrete Cᵒᵖ)
    (P : S3048SignTorsorFiber U) :
    S3049TorsorIso U ((S3076QPrimeMap (𝟙 U)).obj P) P where
  hom := pullback.fst (f := P.projection)
    (g := (((𝟙 U : Discrete (U.as ⟶ U.as))).as).unop)
  comm := by
    dsimp [S3076QPrimeMap, S3075PullbackFunctor, S3073PullbackFiber,
      S3073PullbackProjection]
    exact pullback.condition
  equivariant := by
    intro g
    dsimp [S3076QPrimeMap, S3075PullbackFunctor, S3073PullbackFiber,
      S3073PullbackAction]
    exact (pullback.lift_fst _ _ _).symm
  isIso := by
    haveI : IsIso (((𝟙 U : Discrete (U.as ⟶ U.as))).as).unop := by
      rw [S3076MapIdArrowUnop]
      infer_instance
    exact inferInstance

#check S3076MapIdArrow
#check S3076MapIdObj
#print axioms S3076MapIdObj


theorem S3076MapIdObj_natural (U : LocallyDiscrete Cᵒᵖ)
    {P Q : S3048SignTorsorFiber U} (h : P ⟶ Q) :
    (((S3075PullbackFunctor (𝟙 U)).map h).hom) ≫ (S3076MapIdObj U Q).hom =
      (S3076MapIdObj U P).hom ≫ h.hom := by
  dsimp [S3075PullbackFunctor, S3076MapIdObj, S3074MapIso, S3074Map]
  simp only [pullback.lift_fst]

#check S3076MapIdObj_natural
#print axioms S3076MapIdObj_natural


noncomputable def S3076TorsorIsoInv
    {U : LocallyDiscrete Cᵒᵖ} {P Q : S3048SignTorsorFiber U}
    (f : S3049TorsorIso U P Q) : S3049TorsorIso U Q P := by
  haveI : IsIso f.hom := f.isIso
  refine
    { hom := CategoryTheory.inv f.hom
      comm := ?_
      equivariant := ?_
      isIso := by infer_instance }
  · calc
      CategoryTheory.inv f.hom ≫ P.projection
          = CategoryTheory.inv f.hom ≫ (f.hom ≫ Q.projection) := by rw [f.comm]
      _ = (CategoryTheory.inv f.hom ≫ f.hom) ≫ Q.projection := by rw [Category.assoc]
      _ = Q.projection := by rw [IsIso.inv_hom_id, Category.id_comp]
  · intro g
    have hf : f.hom ≫ Q.action g = P.action g ≫ f.hom :=
      f.equivariant g
    rw [IsIso.inv_comp_eq]
    rw [← Category.assoc, hf, Category.assoc]
    simp

#check S3076TorsorIsoInv


noncomputable def S3076MapIdIsoObj (U : LocallyDiscrete Cᵒᵖ)
    (P : S3048SignTorsorFiber U) :
    (S3075PullbackFunctor (𝟙 U)).obj P ≅ P :=
  Iso.mk (S3076MapIdObj U P) (S3076TorsorIsoInv (S3076MapIdObj U P))
    (by
      apply S3049TorsorIso.ext
      simp [S3076MapIdObj, S3076TorsorIsoInv])
    (by
      apply S3049TorsorIso.ext
      simp [S3076MapIdObj, S3076TorsorIsoInv])

noncomputable def S3076MapId (U : LocallyDiscrete Cᵒᵖ) :
    S3075PullbackFunctor (𝟙 U) ≅
      CategoryTheory.Functor.id (S3048SignTorsorFiber U) :=
  NatIso.ofComponents
    (fun P => S3076MapIdIsoObj U P)
    (by
      intro P Q h
      apply S3049TorsorIso.ext
      exact S3076MapIdObj_natural U h)

#check S3076MapId
#print axioms S3076MapId

end LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual