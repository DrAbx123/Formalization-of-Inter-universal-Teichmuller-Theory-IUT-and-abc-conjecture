import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ABCBridge.InvariantsDescent

open scoped TensorProduct

noncomputable section

universe u

variable (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-- The fixed-point subalgebra `A^G`. -/
def fixedPointSubalgebra : Subalgebra R A := FixedPoints.subalgebra R A G

instance : SMulCommClass G (fixedPointSubalgebra R A G) A :=
  inferInstanceAs (SMulCommClass G (FixedPoints.subalgebra R A G) A)

/-- The inclusion `A^G → A`. -/
def fixedPointInclusion : fixedPointSubalgebra R A G →ₐ[R] A :=
  (fixedPointSubalgebra R A G).val

/-- Base-change fixed points: the canonical `S`-linear map
`S ⊗[R] A^G → S ⊗[R] A`.  It is injective when `S` is flat over `R`. -/
theorem fixedPoints_baseChange_inclusion_injective
    (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S] :
    Function.Injective
      (LinearMap.lTensor S (fixedPointInclusion R A G).toLinearMap) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (fun _ _ h => Subtype.ext h)

/-- Faithfully-flat descent for the fixed-point subalgebra: if after a faithfully
flat base change `S/R` the fixed-point algebra is identified with an `S`-étale
algebra `T`, then `A^G` is étale over `R`. -/
theorem etale_fixedPointSubalgebra_of_baseChange_fixedPoints
    (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.FaithfullyFlat R S] [Algebra.Etale S T]
    (e : S ⊗[R] fixedPointSubalgebra R A G ≃ₐ[S] T) :
    Algebra.Etale R (fixedPointSubalgebra R A G) := by
  haveI : Algebra.Etale S (S ⊗[R] fixedPointSubalgebra R A G) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (R := R)
    (S := fixedPointSubalgebra R A G) S

/-- The descended algebra is flat over `R`. -/
theorem flat_fixedPointSubalgebra_of_baseChange_fixedPoints
    (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.FaithfullyFlat R S] [Algebra.Etale S T]
    (e : S ⊗[R] fixedPointSubalgebra R A G ≃ₐ[S] T) :
    Module.Flat R (fixedPointSubalgebra R A G) := by
  haveI := etale_fixedPointSubalgebra_of_baseChange_fixedPoints R A G S T e
  exact Algebra.Smooth.flat R (fixedPointSubalgebra R A G)

/-- The descended algebra is formally unramified over `R`. -/
theorem formallyUnramified_fixedPointSubalgebra_of_baseChange_fixedPoints
    (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.FaithfullyFlat R S] [Algebra.Etale S T]
    (e : S ⊗[R] fixedPointSubalgebra R A G ≃ₐ[S] T) :
    Algebra.FormallyUnramified R (fixedPointSubalgebra R A G) := by
  haveI := etale_fixedPointSubalgebra_of_baseChange_fixedPoints R A G S T e
  infer_instance

/-- The descended algebra is finitely presented over `R`. -/
theorem finitePresentation_fixedPointSubalgebra_of_baseChange_fixedPoints
    (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.FaithfullyFlat R S] [Algebra.Etale S T]
    (e : S ⊗[R] fixedPointSubalgebra R A G ≃ₐ[S] T) :
    Algebra.FinitePresentation R (fixedPointSubalgebra R A G) := by
  haveI := etale_fixedPointSubalgebra_of_baseChange_fixedPoints R A G S T e
  infer_instance

end

end ABCBridge.InvariantsDescent
