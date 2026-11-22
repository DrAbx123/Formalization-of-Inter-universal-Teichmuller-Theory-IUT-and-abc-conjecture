import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3069QPrimeTorsorStack
import tmp.sheaf.xif.paper.S3042bUnconditionalQEffectiveDescent
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3072QPrimePseudofunctor
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
namespace LeanFormal.IUT.XiFPaper.S3076QPrimeAssemblyActual

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K

/-- The strict functor associated to a Q' pseudofunctor target. -/
noncomputable def S3076StrictFunctor (T : S3072QPrimePseudofunctorTarget) :
    Cᵒᵖ ⥤ Cat where
  obj U := T.obj (LocallyDiscrete.mk U)
  map {U V} f := T.map (LocallyDiscrete.mk f)
  map_id U := by
    simpa using T.mapId_coherent (LocallyDiscrete.mk U)
  map_comp {U V W} f g := by
    simpa using T.mapComp_coherent (LocallyDiscrete.mk f) (LocallyDiscrete.mk g)

/-- Q' pseudofunctor assembled from a target. -/
noncomputable def S3076QPrimeOfTarget (T : S3072QPrimePseudofunctorTarget) :
    Iut.EtaleStackPseudofunctor S2994A6K :=
  (S3076StrictFunctor T).toPseudofunctor'

/-- IsStack target for the assembled Q'. -/
def S3076QPrimeIsStackTarget (Q : Iut.EtaleStackPseudofunctor S2994A6K) : Prop :=
  Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

#check S3076StrictFunctor
#check S3076QPrimeOfTarget
#check S3076QPrimeIsStackTarget

end LeanFormal.IUT.XiFPaper.S3076QPrimeAssemblyActual