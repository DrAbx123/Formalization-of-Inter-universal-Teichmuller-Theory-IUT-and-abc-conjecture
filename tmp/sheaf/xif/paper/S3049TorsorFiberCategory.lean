import tmp.sheaf.xif.paper.S3048StackificationQPrime

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory

/-- Equivariant isomorphism of sign-torsor fibers over U. -/
structure S3049TorsorIso
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ)
    (P Q : S3048SignTorsorFiber U) where
  hom : P.total ⟶ Q.total
  comm : hom ≫ Q.projection = P.projection
  equivariant : ∀ g : SignGroup, hom ≫ Q.action g = P.action g ≫ hom
  isIso : IsIso hom

/-- Structure data for the torsor fiber groupoid, with the exact object and
hom types as fields.  Coherence of a full Category instance is the next
missing construction step. -/
structure S3049TorsorFiberCategoryData
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) where
  objects : Type 1
  objects_eq : objects = S3048SignTorsorFiber U
  hom : objects → objects → Type
  hom_eq : ∀ P Q, hom P Q = S3049TorsorIso U
    (cast objects_eq P) (cast objects_eq Q)

/-- Exact target: each test object has the sign-torsor fiber groupoid. -/
def S3049TorsorFiberCategoryTarget : Prop :=
  ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
    Nonempty (S3049TorsorFiberCategoryData U)

/-- Exact target for Q': fiberwise torsor groupoid data and IsStack. -/
structure S3049StackificationQPrimeTarget where
  Qprime : Iut.EtaleStackPseudofunctor S2994A6K
  fiber_category :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (S3049TorsorFiberCategoryData U)
  isStack : Qprime.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

#check S3049TorsorIso
#check S3049TorsorFiberCategoryData
#check S3049TorsorFiberCategoryTarget
#check S3049StackificationQPrimeTarget

end LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
end
