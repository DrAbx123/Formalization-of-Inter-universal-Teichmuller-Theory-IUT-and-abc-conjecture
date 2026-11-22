import tmp.sheaf.xif.paper.S2056MaxAbelianBridge
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section
set_option maxHeartbeats 2000000
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2056MaxAbelianBridge
open IntermediateField

namespace Probe

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p)

local notation "E" => localField p U
local notation "Ω" => AlgebraicClosure ℚ_[p]

example (x : maximalAbelianExtension p U) : IsIntegral E (x : Ω) := by
  have h1 : IsIntegral ℚ_[p] (x : Ω) := Algebra.IsIntegral.isIntegral _
  exact h1.tower_top

example : IsGalois E (maximalAbelianExtension p U) := by
  haveI hfix : (maximalAbelianExtension p U).fixingSubgroup.Normal := by
    rw [fixingSubgroup_maximalAbelianExtension p U]
    exact commutatorClosed_normal p U
  exact (InfiniteGalois.normal_iff_isGalois (maximalAbelianExtension p U)).mp hfix

example (x : maximalAbelianExtension p U) :
    ∃ (L : PadicField.AbFin E Ω), (x : Ω) ∈ L.1 := by
  let L0 : IntermediateField E Ω := IntermediateField.adjoin E {(x : Ω)}
  have hxint : IsIntegral E (x : Ω) := by
    have h1 : IsIntegral ℚ_[p] (x : Ω) := Algebra.IsIntegral.isIntegral _
    exact h1.tower_top
  haveI hL0fd : FiniteDimensional E L0 := IntermediateField.adjoin.finiteDimensional hxint
  let L : IntermediateField E Ω := IntermediateField.normalClosure E L0 Ω
  haveI hLfd : FiniteDimensional E L := normalClosure.is_finiteDimensional E L0 Ω
  have hL0M : L0 ≤ maximalAbelianExtension p U := IntermediateField.adjoin_simple_le_iff.mpr x.2
  haveI hGalM : IsGalois E (maximalAbelianExtension p U) := by
    haveI hfix : (maximalAbelianExtension p U).fixingSubgroup.Normal := by
      rw [fixingSubgroup_maximalAbelianExtension p U]
      exact commutatorClosed_normal p U
    exact (InfiniteGalois.normal_iff_isGalois (maximalAbelianExtension p U)).mp hfix
  haveI hNormalM : Normal E (maximalAbelianExtension p U) := IsGalois.to_normal
  have hLM : L ≤ maximalAbelianExtension p U := IntermediateField.normalClosure_le_iff_of_normal.mpr hL0M
  haveI hGalL : IsGalois E L := inferInstance
  haveI hAbM : IsAbelianGalois E (maximalAbelianExtension p U) :=
    { toIsGalois := hGalM
      toIsMulCommutative := ⟨⟨fun σ τ => mul_comm σ τ⟩⟩ }
  haveI hAbL : IsAbelianGalois E L := IsAbelianGalois.of_algHom (IntermediateField.inclusion hLM)
  exact ⟨⟨L, hLfd, hAbL⟩, IntermediateField.le_normalClosure L0 (IntermediateField.mem_adjoin_simple_self E (x : Ω))⟩

end Probe
