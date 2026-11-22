import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3069QPrimeTorsorStack
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
namespace LeanFormal.IUT.XiFPaper.S3076QPrimePseudofunctorActual

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K

/-- Q' object-level fiber. -/
noncomputable abbrev S3076QPrimeObj (U : LocallyDiscrete Cᵒᵖ) : Cat :=
  S3069FiberCat U

/-- Q' object map: pullback of sign-torsors along a test morphism. -/
noncomputable abbrev S3076QPrimeMap
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    S3076QPrimeObj U ⥤ S3076QPrimeObj V :=
  S3075PullbackFunctor f

/-- First missing coherence: map of identity is the identity functor. -/
def S3076QPrimeMapIdCoherent : Prop :=
  ∀ U : LocallyDiscrete Cᵒᵖ,
    S3076QPrimeMap (𝟙 U) = CategoryTheory.Functor.id (S3076QPrimeObj U).α

/-- Second missing coherence: map of composition is composition of maps. -/
def S3076QPrimeMapCompCoherent : Prop :=
  ∀ {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
    S3076QPrimeMap (f ≫ g) =
      S3076QPrimeMap f ⋙ S3076QPrimeMap g

/-- The full Q' pseudofunctor target, after supplying the two coherence fields. -/
def S3076QPrimePseudofunctorTarget : Prop :=
  S3076QPrimeMapIdCoherent ∧ S3076QPrimeMapCompCoherent

/-- IsStack target for Q'. -/
def S3076QPrimeIsStackTarget (Q : Iut.EtaleStackPseudofunctor S2994A6K) : Prop :=
  Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

#check S3076QPrimeObj
#check S3076QPrimeMap
#check S3076QPrimeMapIdCoherent
#check S3076QPrimeMapCompCoherent
#check S3076QPrimePseudofunctorTarget
#check S3076QPrimeIsStackTarget

end LeanFormal.IUT.XiFPaper.S3076QPrimePseudofunctorActual