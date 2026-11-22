import tmp.sheaf.xif.paper.S2994A6Stackification
import tmp.sheaf.xif.paper.S2993A6QIsStackNoGo

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2993A6QIsStackNoGo
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2993A6StackificationSpec

/-- Exact A6 functorial pointwise colimit spec: a pseudofunctor with the
pointwise action-groupoid fibers, plus explicit mapId/mapComp coherence data. -/
structure S2993A6FunctorialPointwiseColimitSpec where
  Q : Iut.EtaleStackPseudofunctor S2994A6K
  pointwise_equiv :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (Q.obj U)
        (S2994A6PointwiseQuotient U))
  mapId_coherent :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (Q.map (𝟙 U) ≅ 𝟙 (Q.obj U))
  mapComp_coherent :
    ∀ {U V W : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
      (f : U ⟶ V) (g : V ⟶ W),
      Nonempty (Q.map (f ≫ g) ≅ Q.map f ≫ Q.map g)

/-- Exact A6 stackification spec: pointwise colimit plus IsStack for the
torsor/quotient stack.  This is a target, not asserted. -/
structure S2993A6StackificationSpec
    extends S2993A6FunctorialPointwiseColimitSpec where
  isStack :
    toS2993A6FunctorialPointwiseColimitSpec.Q.IsStack
      (Iut.SchemeOverField.etaleTopology S2994A6K)
  torsor_fiber :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence
        (toS2993A6FunctorialPointwiseColimitSpec.Q.obj U)
        (S2994A6PointwiseQuotient U))

/-- The exact stackification target (not a proof). -/
def S2993A6StackificationTarget : Prop :=
  Nonempty S2993A6StackificationSpec

/-- The no-go obstruction refutes the raw pointwise prestack being a stack. -/
theorem S2993A6_QIsStack_no_go
    (H : S2993TrivialSignTorsorObstruction) :
    ¬ S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F) :=
  S2993_not_isStack_of_obstruction H

#check S2993A6FunctorialPointwiseColimitSpec
#check S2993A6StackificationSpec
#check S2993A6StackificationTarget
#check S2993A6_QIsStack_no_go

end LeanFormal.IUT.XiFPaper.S2993A6StackificationSpec
end
