/- U-L: explicit actual tensor field factors from etale decomposition. -/
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicEtaleTensorDecomposition
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULTensorFactorsActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldPadicTensor LeanFormal.IUT.NumberFieldFinitePlace
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι -> Type w}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
structure ULTensorFactorData (A : ι -> Type w) where
  J : Type (max u w)
  fintype : Fintype J
  E : J -> Type (max u w)
  field : ∀ j, NontriviallyNormedField (E j)
  alg : ∀ j, NormedAlgebra ℚ_[p] (E j)
  equiv : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) -> E j)
  finite : ∀ j, FiniteDimensional ℚ_[p] (E j)
  complete : ∀ j, CompleteSpace (E j)
  ultrametric : ∀ j, IsUltrametricDist (E j)
noncomputable def ulTensorFactorsOfEtale (A : ι -> Type w)
    [∀ i, NormedCommRing (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
    [∀ i, FiniteDimensional ℚ_[p] (A i)] [∀ i, Algebra.Etale ℚ_[p] (A i)] :
    ULTensorFactorData (p := p) A := by
  classical
  obtain ⟨J, hJ, E, hfield, halg, e, hprops⟩ :=
    exists_finiteNormedFieldProduct_etaleTensor (p := p) A
  exact {
    J := J, fintype := hJ, E := E, field := hfield, alg := halg, equiv := e,
    finite := fun j => (hprops.1 j).1,
    complete := fun j => (hprops.1 j).2.1,
    ultrametric := fun j => (hprops.1 j).2.2 }
noncomputable def ulTensorFactorsOfPlaces (tuple : (i : ι) -> V i) :
    ULTensorFactorData (p := p) (fun i => CommonPrimeCompletion (places i (tuple i))) := by
  letI : ∀ i, Algebra.FormallyEtale ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
    fun _ => Algebra.FormallyEtale.of_isSeparable _ _
  letI : ∀ i, Algebra.Etale ℚ_[p] (CommonPrimeCompletion (places i (tuple i))) :=
    fun _ => ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact ulTensorFactorsOfEtale (p := p) (fun i => CommonPrimeCompletion (places i (tuple i)))
#print axioms ulTensorFactorsOfEtale
end LeanFormal.IUT.XiFPaper.Mzk1ULTensorFactorsActual
