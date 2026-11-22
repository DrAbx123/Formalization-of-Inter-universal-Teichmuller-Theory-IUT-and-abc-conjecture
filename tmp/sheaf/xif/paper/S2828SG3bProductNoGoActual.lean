import tmp.sheaf.xif.paper.S2827SG3bProductHaarActual
import tmp.sheaf.xif.paper.S349C3TensorLatticeRegionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2828SG3bProductNoGoActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- A non-additivity witness for the pure-tensor log-shell region: two region
points whose sum is outside the region. -/
def S2828NotAdditiveWitness : Prop :=
  ∃ x ∈ actualC3LogShellTensorRegion C3,
    ∃ y ∈ actualC3LogShellTensorRegion C3,
      x + y ∉ actualC3LogShellTensorRegion C3

/-- A Cartesian-product decomposition of the pure-tensor region under a linear
equivalence, with additive local factors. -/
def S2828ProductDecomposition
    {J : Type} [Fintype J] {E : J -> Type}
    [forall j, AddCommGroup (E j)] [forall j, Module ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]] ((j : J) -> E j))
    (localRegion : (j : J) -> Set (E j)) : Prop :=
  e '' actualC3LogShellTensorRegion C3 = Set.pi Set.univ localRegion

/-- If there is a non-additivity witness, no Cartesian-product decomposition
with additive local factors can exist.  This is the exact no-go criterion. -/
theorem S2828_no_product_decomposition_of_not_additive
    (w : S2828NotAdditiveWitness C3)
    {J : Type} [Fintype J] {E : J -> Type}
    [forall j, AddCommGroup (E j)] [forall j, Module ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]] ((j : J) -> E j))
    (localRegion : (j : J) -> Set (E j))
    (hadd : forall j (a : E j), a ∈ localRegion j ->
      forall (b : E j), b ∈ localRegion j -> a + b ∈ localRegion j)
    (h : S2828ProductDecomposition C3 e localRegion) : False := by
  rcases w with ⟨x, hx, y, hy, hxy⟩
  have hxE : e x ∈ Set.pi Set.univ localRegion := by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hyE : e y ∈ Set.pi Set.univ localRegion := by
    rw [← h]
    exact ⟨y, hy, rfl⟩
  have hsum : e x + e y ∈ Set.pi Set.univ localRegion := by
    rw [Set.mem_pi] at hxE hyE ⊢
    intro j _
    exact hadd j _ (hxE j (Set.mem_univ j)) _ (hyE j (Set.mem_univ j))
  have hsum_image : e x + e y ∈ e '' actualC3LogShellTensorRegion C3 := by
    rw [h]
    exact hsum
  rcases hsum_image with ⟨z, hz, hz_eq⟩
  have hzx : z = x + y := by
    apply e.injective
    rw [map_add, hz_eq]
  refine hxy ?_
  rw [← hzx]
  exact hz

/-- A product decomposition with additive local factors forces the pure-tensor
region to be additive.  This is the exact structural consequence; an
unconditional no-go is then equivalent to non-additivity of the region. -/
theorem S2828_additive_of_productDecomposition
    {J : Type} [Fintype J] {E : J -> Type}
    [forall j, AddCommGroup (E j)] [forall j, Module ℚ_[C3.p] (E j)]
    (e : C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]] ((j : J) -> E j))
    (localRegion : (j : J) -> Set (E j))
    (hadd : forall j (a : E j), a ∈ localRegion j ->
      forall (b : E j), b ∈ localRegion j -> a + b ∈ localRegion j)
    (h : S2828ProductDecomposition C3 e localRegion) :
    forall (x : C3LogShellTensorBlock C3),
      x ∈ actualC3LogShellTensorRegion C3 ->
      forall (y : C3LogShellTensorBlock C3),
        y ∈ actualC3LogShellTensorRegion C3 ->
        x + y ∈ actualC3LogShellTensorRegion C3 := by
  intro x hx y hy
  have hxE : e x ∈ Set.pi Set.univ localRegion := by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hyE : e y ∈ Set.pi Set.univ localRegion := by
    rw [← h]
    exact ⟨y, hy, rfl⟩
  have hsum : e x + e y ∈ Set.pi Set.univ localRegion := by
    rw [Set.mem_pi] at hxE hyE ⊢
    intro j _
    exact hadd j _ (hxE j (Set.mem_univ j)) _ (hyE j (Set.mem_univ j))
  have hsum_image : e x + e y ∈ e '' actualC3LogShellTensorRegion C3 := by
    rw [h]
    exact hsum
  rcases hsum_image with ⟨z, hz, hz_eq⟩
  have hzx : z = x + y := by
    apply e.injective
    rw [map_add, hz_eq]
  rw [← hzx]
  exact hz

#check S2828NotAdditiveWitness
#check S2828ProductDecomposition
#check S2828_no_product_decomposition_of_not_additive
#check S2828_additive_of_productDecomposition
#print axioms S2828_additive_of_productDecomposition
#print axioms S2828_no_product_decomposition_of_not_additive

end LeanFormal.IUT.XiFPaper.S2828SG3bProductNoGoActual
end
