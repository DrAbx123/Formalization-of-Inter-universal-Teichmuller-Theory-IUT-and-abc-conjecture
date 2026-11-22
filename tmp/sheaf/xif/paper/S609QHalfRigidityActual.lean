import tmp.sheaf.xif.paper.S531EtThThetaUnitRecipeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S609QHalfRigidityActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S531EtThThetaUnitRecipeActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem qHalf_ratio_sq_one
    (a c : (ACF T b)ˣ)
    (ha : a ^ 2 = qUnit T b) (hc : c ^ 2 = qUnit T b) :
    (a * c⁻¹) ^ 2 = 1 := by
  rw [mul_pow, inv_pow, ha, hc, mul_inv_cancel]

theorem qHalf_constant_multiple_rigidity
    (a c : (ACF T b)ˣ)
    (ha : a ^ 2 = qUnit T b) (hc : c ^ 2 = qUnit T b) :
    ∃ u : (ACF T b)ˣ, u ^ 2 = 1 ∧ c = a * u := by
  refine ⟨a⁻¹ * c, ?_, ?_⟩
  · rw [mul_pow, inv_pow, ha, hc, inv_mul_cancel]
  · group

theorem qHalf_ratio_mem_rootsOfUnity
    (a c : (ACF T b)ˣ)
    (ha : a ^ 2 = qUnit T b) (hc : c ^ 2 = qUnit T b) :
    (a * c⁻¹) ∈ rootsOfUnity 2 (ACF T b) := by
  rw [mem_rootsOfUnity]
  exact qHalf_ratio_sq_one (T := T) (b := b) a c ha hc

structure QHalfSpecialPointNormalizationGap where
  evalSection : ConversePoint T b → ACF T b
  specialPoint : ConversePoint T b
  specialPoint_two_torsion : specialPoint + specialPoint = 0
  normalization_eq : Prop
  evalSplitting_equivariant : Prop
  kummerClass_eq : Prop

def QHalfSpecialPointNormalizationGapRequired : Prop :=
  Nonempty (QHalfSpecialPointNormalizationGap (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.S609QHalfRigidityActual
end