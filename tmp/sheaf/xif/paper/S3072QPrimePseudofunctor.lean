import tmp.sheaf.xif.paper.S3071TorsorGroupoid

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3071TorsorGroupoid
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3072QPrimePseudofunctor

/-- Pullback of sign-torsors along a test morphism f : U ⟶ V.
The functor goes from fibers over V to fibers over U (opposite-category
direction).  This is the exact missing construction. -/
structure S3072TorsorPullback
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) where
  pullbackFunctor :
    S3048SignTorsorFiber V ⥤ S3048SignTorsorFiber U

/-- Object-level Q' fiber: the actual torsor groupoid. -/
noncomputable abbrev S3072QPrimeObj
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) : Cat :=
  S3069FiberCat U

/-- Exact target for the Q' pseudofunctor: object-level fibers, pullback
functors, and mapId/mapComp coherence. -/
structure S3072QPrimePseudofunctorTarget where
  obj : (LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) → Cat
  obj_eq : ∀ U, obj U = S3072QPrimeObj U
  map : ∀ {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V), obj V ⥤ obj U
  map_pullback :
    ∀ {U V} (f : U ⟶ V), Nonempty (S3072TorsorPullback f)
  mapId_coherent :
    ∀ U, map (𝟙 U) = CategoryTheory.Functor.id (obj U).α
  mapComp_coherent :
    ∀ {U V W} (f : U ⟶ V) (g : V ⟶ W),
      map (f ≫ g) = map g ⋙ map f
  stack_target : Prop

def S3072QPrimePseudofunctorProp : Prop :=
  Nonempty S3072QPrimePseudofunctorTarget

#check S3072TorsorPullback
#check S3072QPrimeObj
#check S3072QPrimePseudofunctorTarget
#check S3072QPrimePseudofunctorProp

end LeanFormal.IUT.XiFPaper.S3072QPrimePseudofunctor
end
