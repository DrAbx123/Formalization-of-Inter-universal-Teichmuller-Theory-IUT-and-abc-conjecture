/-
# Consumer model for L1-F1: finite étale K-algebras vs finite continuous G_K-sets

Temporary stage-2 glue for SHEAF node L1-F1. It turns the already proved assembly
`LeanFormal.IUT.IUTII.Frobenioid.Example36GSetEtaleEquivalenceAssembly` into the two
declarations that the actual consumer
`Example36FiberAutomorphism.fiberAutMulEquivOfFiberCorrespondence` expects:

* `finiteEtaleContinuousGaloisSetsEquivalence K`: the field Galois correspondence
  `(CommAlgCat.FiniteEtale.{u} K)^op ≌ FiniteContinuousGaloisSetCategory K` composed
  with the open-stabilizer comparison, giving the Mathlib `ContAction` model
  `finiteContinuousGaloisSetsOfField K`;
* `finiteEtaleContinuousGaloisSetsFiberIso K`: the fiber identification
  `fieldFiber K ≅ equivalence.functor ⋙ finiteContinuousGaloisSetFiber G_K`,
  read off from the assembly's `finiteEtaleFiberIsoContinuous`.

No new mathematics, no placeholders, no assumed data. This file is a tmp artifact; it is
outside the production build closure, and wiring it into
`Example36FiberAutomorphism.lean` is a separate edit owned by that file.
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36GSetEtaleEquivalenceAssembly

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace L1F1

open CategoryTheory

universe u

/-- The L1-F1 equivalence on Mathlib's model of finite continuous `G_K`-sets:
the assembled equivalence between finite étale `K`-algebras and the
open-stabilizer full subcategory, composed with the (inverse of the)
open-stabilizer/continuous-action comparison. -/
noncomputable def finiteEtaleContinuousGaloisSetsEquivalence (K : Type u) [Field K] :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ finiteContinuousGaloisSetsOfField K :=
  (finiteEtaleContinuousEquivalenceFinal (K := K)).trans
    (continuousActionEquivalenceOpenStabilizers (Iut.AbsoluteGaloisProfinite K)).symm

/-- The L1-F1 fiber identification transported to the composed equivalence:
the assembly's fiber iso `finiteEtaleFiberIsoContinuous` has exactly this type,
because `(finiteEtaleContinuousGaloisSetsEquivalence K).functor` is the assembly's
continuous functor. -/
noncomputable def finiteEtaleContinuousGaloisSetsFiberIso (K : Type u) [Field K] :
    fieldFiber K ≅
      (finiteEtaleContinuousGaloisSetsEquivalence K).functor ⋙
        finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K) :=
  finiteEtaleFiberIsoContinuous (K := K)

end L1F1
end LeanFormal.IUT.IUTII.Frobenioid.Example36
