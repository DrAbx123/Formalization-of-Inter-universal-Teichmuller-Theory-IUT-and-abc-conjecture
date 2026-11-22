import tmp.sheaf.xif.paper.S2994A6Stackification
import tmp.sheaf.xif.paper.S2899A6QPrestackActual
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
namespace LeanFormal.IUT.XiFPaper.S2996A6StackWitnessConstruction

/-- The stack witness core: a pseudofunctor with the A6 pointwise fibers. -/
structure S2995A6StackWitnessCore where
  stack : Iut.EtaleStackPseudofunctor S2994A6K
  fiber_equiv : ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
    Nonempty (CategoryTheory.Equivalence (stack.obj U)
      (S2994A6PointwiseQuotient U))

/-- Extended witness: core plus prestack and stackification fields. -/
structure S2995A6StackWitness where
  stack : Iut.EtaleStackPseudofunctor S2994A6K
  fiber_equiv : ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
    Nonempty (CategoryTheory.Equivalence (stack.obj U)
      (S2994A6PointwiseQuotient U))
  prestack : Pseudofunctor.IsPrestack stack
    (Iut.SchemeOverField.etaleTopology S2994A6K)
  stackification : Pseudofunctor.IsStack stack
    (Iut.SchemeOverField.etaleTopology S2994A6K)

/-- Actual core: S2882A6Q itself has exactly the A6 pointwise fibers. -/
noncomputable def S2996A6StackWitnessCore : S2995A6StackWitnessCore where
  stack := S2882A6Q
  fiber_equiv U := ⟨CategoryTheory.Equivalence.refl⟩

/-- Every actual witness core extends by supplying the two missing Prop fields. -/
noncomputable def S2996A6StackWitnessCore.toWitness
    (C : S2995A6StackWitnessCore)
    (hP : Pseudofunctor.IsPrestack C.stack
      (Iut.SchemeOverField.etaleTopology S2994A6K))
    (hS : Pseudofunctor.IsStack C.stack
      (Iut.SchemeOverField.etaleTopology S2994A6K)) :
    S2995A6StackWitness where
  stack := C.stack
  fiber_equiv := C.fiber_equiv
  prestack := hP
  stackification := hS

#check S2995A6StackWitnessCore
#check S2995A6StackWitness
#check S2996A6StackWitnessCore
#check S2996A6StackWitnessCore.toWitness
#print axioms S2996A6StackWitnessCore
#print axioms S2996A6StackWitnessCore.toWitness

end LeanFormal.IUT.XiFPaper.S2996A6StackWitnessConstruction