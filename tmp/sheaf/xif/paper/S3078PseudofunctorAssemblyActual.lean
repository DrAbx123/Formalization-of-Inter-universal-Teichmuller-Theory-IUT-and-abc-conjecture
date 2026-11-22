import tmp.sheaf.xif.paper.S3078QPrimePseudofunctorTarget
import tmp.sheaf.xif.paper.S3078MapCompNatIsoActual
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3078QPrimePseudofunctorTarget
open LeanFormal.IUT.XiFPaper.S3078MapCompNatIsoActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
namespace LeanFormal.IUT.XiFPaper.S3078PseudofunctorAssemblyActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable def S3078MapComp
    {U V W : LocallyDiscrete S3078Kᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    S3078PrelaxFunctor.map (f ≫ g) ≅
      S3078PrelaxFunctor.map f ≫ S3078PrelaxFunctor.map g :=
  Cat.Hom.isoMk (S3078MapCompNatIso f g)

noncomputable def S3078PseudofunctorOfCoherence
    (C : S3078PseudofunctorCoherenceTarget S3078PrelaxFunctor
      S3078MapId (fun {a b c} f g => S3078MapComp f g)) :
    Pseudofunctor (LocallyDiscrete S3078Kᵒᵖ) Cat.{0, 1} :=
  S3078PseudofunctorAssemblyTemplate S3078PrelaxFunctor S3078MapId
    (fun {a b c} f g => S3078MapComp f g) C

/-- IsStack target for the assembled Q'. -/
def S3078QPrimeIsStackTarget
    (Q : Pseudofunctor (LocallyDiscrete S3078Kᵒᵖ) Cat.{0, 1}) : Prop :=
  Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

#check S3078MapComp
#check S3078PseudofunctorOfCoherence
#check S3078QPrimeIsStackTarget

end LeanFormal.IUT.XiFPaper.S3078PseudofunctorAssemblyActual