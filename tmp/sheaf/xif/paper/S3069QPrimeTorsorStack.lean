import tmp.sheaf.xif.paper.S3049TorsorFiberCategory

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack

@[ext]
theorem S3049TorsorIso.ext
    {U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    {P Q : S3048SignTorsorFiber U} {f g : S3049TorsorIso U P Q}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp only at h
  subst h
  rfl

instance S3069CategoryStruct
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) :
    CategoryStruct (S3048SignTorsorFiber U) where
  Hom P Q := S3049TorsorIso U P Q
  id P :=
    { hom := 𝟙 P.total
      comm := by simp
      equivariant := by intro g; simp
      isIso := inferInstance }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by rw [Category.assoc, g.comm, f.comm]
      equivariant := by
        intro h
        rw [Category.assoc, g.equivariant, ← Category.assoc,
          f.equivariant, Category.assoc]
      isIso := by
        haveI : IsIso f.hom := f.isIso
        haveI : IsIso g.hom := g.isIso
        exact inferInstance }

instance S3069Category
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) :
    Category (S3048SignTorsorFiber U) where
  id_comp f := by apply S3049TorsorIso.ext; rfl
  comp_id f := by apply S3049TorsorIso.ext; rfl
  assoc f g h := by apply S3049TorsorIso.ext; rfl

noncomputable abbrev S3069FiberCat
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) : Cat :=
  Cat.of (S3048SignTorsorFiber U)

/-- First missing construction: pullback of a sign-torsor along a test
morphism, needed for the Q' pseudofunctor map. -/
structure S3069TorsorPullbackData
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) where
  pullbackFiber : S3048SignTorsorFiber U → S3048SignTorsorFiber V
  pullbackFunctor : S3048SignTorsorFiber U ⥤ S3048SignTorsorFiber V
  pullbackFunctor_obj : ∀ P, pullbackFunctor.obj P = pullbackFiber P

def S3069QPrimeMapTarget
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) : Prop :=
  Nonempty (S3069TorsorPullbackData f)

/-- Exact target for Q' as a pseudofunctor: fibers are torsor groupoids and
each test morphism has a pullback functor with coherence. -/
structure S3069QPrimeTarget where
  Qprime : Iut.EtaleStackPseudofunctor S2994A6K
  fiber_eq : ∀ U,
    Nonempty (CategoryTheory.Equivalence (Qprime.obj U)
      (S3069FiberCat U))
  map_target : ∀ {U V} (f : U ⟶ V),
    S3069QPrimeMapTarget f
  isStack : Qprime.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

#check S3069CategoryStruct
#check S3069Category
#check S3069FiberCat
#check S3069TorsorPullbackData
#check S3069QPrimeTarget

end LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
end
