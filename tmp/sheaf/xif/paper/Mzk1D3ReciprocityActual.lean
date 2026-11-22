import Reciprocity.Abelian
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1D3ReciprocityActual

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω]

/-- Actual local reciprocity interface on a finite abelian extension. -/
structure D3ReciprocityData (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] where
  reciprocityMap : Kˣ →* (L ≃ₐ[K] L)
  reciprocityMap_eq : reciprocityMap = PadicField.abRec p L
  kernel_eq : reciprocityMap.ker = PadicField.normGroup K L
  surjective : Function.Surjective reciprocityMap
  unitNormEquiv : (Kˣ ⧸ PadicField.normGroup K L) ≃* (L ≃ₐ[K] L)
  unitNormEquiv_eq : unitNormEquiv = PadicField.abRecEquiv (p := p) L


/-- Actual local reciprocity data from the proved donor theorems: the map is
`PadicField.abRec`, its kernel is the norm group, it is surjective, and the
unit-norm quotient equivalence is `PadicField.abRecEquiv`. -/
noncomputable def d3ReciprocityData (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    D3ReciprocityData (p := p) (K := K) (Ω := Ω) L where
  reciprocityMap := PadicField.abRec p L
  reciprocityMap_eq := rfl
  kernel_eq := PadicField.ker_abRec (p := p) L
  surjective := PadicField.abRec_surjective (p := p) L
  unitNormEquiv := PadicField.abRecEquiv (p := p) L
  unitNormEquiv_eq := rfl

#print axioms d3ReciprocityData

end LeanFormal.IUT.XiFPaper.Mzk1D3ReciprocityActual