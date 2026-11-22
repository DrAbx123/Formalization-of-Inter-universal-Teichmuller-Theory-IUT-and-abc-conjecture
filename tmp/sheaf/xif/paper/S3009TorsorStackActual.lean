import tmp.sheaf.xif.paper.S2812IsStackActual
import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import tmp.sheaf.xif.paper.S2994A6Stackification
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
namespace LeanFormal.IUT.XiFPaper.S3009TorsorStackActual

/-- The actual etale stack underlying the trivial sign-torsor: the
representable stack of the total space X. -/
abbrev S3009TorsorStack : Iut.EtaleStackPseudofunctor S2994A6K :=
  Iut.schemeRepresentableEtalePseudofunctor S2994A6K
    S2844D6F6BaseChangeActual.S2844X

/-- The actual IsStack instance for the trivial sign-torsor total space. -/
instance S3009TorsorStack_isStack :
    S3009TorsorStack.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K) :=
  S2812IsStackActual.schemeRepresentableEtalePseudofunctor_isStack
    S2994A6K S2844D6F6BaseChangeActual.S2844X

/-- Candidate witness for a sign-torsor stack: an actual etale stack together
with its IsStack proof. -/
structure S3009TorsorStackWitness where
  stack : Iut.EtaleStackPseudofunctor S2994A6K
  isStack : stack.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

/-- Actual candidate: the representable total space X with its actual IsStack. -/
noncomputable def S3009TorsorStackWitness.trivial :
    S3009TorsorStackWitness where
  stack := S3009TorsorStack
  isStack := S3009TorsorStack_isStack

/-- Exact missing general torsor stack: a pseudofunctor whose U-points are
SignGroup-torsors over the Q-fiber, not only the trivial total space X. -/
def S3009GeneralTorsorStackMissing : Prop :=
  ∃ S : Iut.EtaleStackPseudofunctor S2994A6K,
    S.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K) ∧
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (S.obj U)
        (S2994A6PointwiseQuotient U))

#check S3009TorsorStack
#check S3009TorsorStack_isStack
#check S3009TorsorStackWitness
#check S3009TorsorStackWitness.trivial
#check S3009GeneralTorsorStackMissing
#print axioms S3009TorsorStackWitness.trivial

end LeanFormal.IUT.XiFPaper.S3009TorsorStackActual