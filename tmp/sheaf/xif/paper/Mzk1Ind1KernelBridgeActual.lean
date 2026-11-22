import tmp.sheaf.xif.paper.Mzk1Ind1KernelIntegersActual
import tmp.sheaf.xif.paper.Mzk1Ind1ValuationDataActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1KernelBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Ind1KernelIntegersActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ValuationDataActual

variable {F : Type} [NormedField F] [IsUltrametricDist F]
variable [Valued F (WithZero (Multiplicative ℤ))]

def kernelToAQuotient :
    (unitValuationHom (F := F)).ker →* AQuotient F :=
  TimesMuQuotient.quotientMap.comp
    (Subgroup.subtype (unitValuationHom (F := F)).ker)


theorem range_kernelToAQuotient_eq
    (h : CommGroup.torsion Fˣ ≤ (unitValuationHom (F := F)).ker) :
    MonoidHom.mrange (kernelToAQuotient (F := F)) =
      (quotientValuationHom (F := F) h).ker.toSubmonoid := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change kernelToAQuotient (F := F) y ∈
      (quotientValuationHom (F := F) h).ker
    rw [MonoidHom.mem_ker]
    simpa [kernelToAQuotient, quotientValuationHom] using
      (MonoidHom.mem_ker.mp y.2)
  · intro hx
    change x ∈ (quotientValuationHom (F := F) h).ker at hx
    rw [MonoidHom.mem_ker] at hx
    let y : Fˣ := Quotient.out x
    have hy : (y : AQuotient F) = x := Quotient.out_eq x
    have hv : quotientValuationHom (F := F) h (y : AQuotient F) =
        unitValuationHom (F := F) y := by
      simp [quotientValuationHom]
    have hyker : y ∈ (unitValuationHom (F := F)).ker := by
      rw [MonoidHom.mem_ker]
      rw [← hy, hv] at hx
      exact hx
    exact ⟨⟨y, hyker⟩, by
      change (y : AQuotient F) = x
      exact hy⟩

#print axioms range_kernelToAQuotient_eq

structure AQuotientKernelBridge
    (v : AQuotient F →* Multiplicative ℤ) where
  range_eq_ker : MonoidHom.mrange (kernelToAQuotient (F := F)) = v.ker.toSubmonoid
  equiv :
    ((unitValuationHom (F := F)).ker ⧸
        (CommGroup.torsion Fˣ).comap
          (Subgroup.subtype (unitValuationHom (F := F)).ker)) ≃* v.ker.toSubmonoid


theorem kernelToAQuotient_ker_eq :
    (kernelToAQuotient (F := F)).ker =
      (CommGroup.torsion Fˣ).comap
        (Subgroup.subtype (unitValuationHom (F := F)).ker) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  change TimesMuQuotient.quotientMap
      ((Subgroup.subtype (unitValuationHom (F := F)).ker) u) = 1 ↔
    ((Subgroup.subtype (unitValuationHom (F := F)).ker) u) ∈
      CommGroup.torsion Fˣ
  constructor
  · intro h
    simpa [MonoidHom.mem_ker, TimesMuQuotient.quotientMap_ker] using h
  · intro h
    simpa [MonoidHom.mem_ker, TimesMuQuotient.quotientMap_ker] using h


instance kernelBridgeComapNormal :
    ((CommGroup.torsion Fˣ).comap
      (Subgroup.subtype (unitValuationHom (F := F)).ker)).Normal :=
  Subgroup.normal_of_comm _

instance kernelBridgeKerNormal :
    (kernelToAQuotient (F := F)).ker.Normal :=
  Subgroup.normal_of_comm _

noncomputable def quotientKernelEquivRange :
    ((unitValuationHom (F := F)).ker ⧸
        (CommGroup.torsion Fˣ).comap
          (Subgroup.subtype (unitValuationHom (F := F)).ker)) ≃*
      MonoidHom.mrange (kernelToAQuotient (F := F)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (kernelToAQuotient_ker_eq).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (kernelToAQuotient (F := F)))

#print axioms quotientKernelEquivRange


#print axioms kernelToAQuotient_ker_eq

#print axioms kernelToAQuotient


noncomputable def AQuotientKernelBridge.ofRange
    (h : CommGroup.torsion Fˣ ≤ (unitValuationHom (F := F)).ker) :
    AQuotientKernelBridge (quotientValuationHom (F := F) h) where
  range_eq_ker := range_kernelToAQuotient_eq (F := F) h
  equiv := (quotientKernelEquivRange (F := F)).trans
    (MulEquiv.submonoidCongr (range_kernelToAQuotient_eq (F := F) h))

#print axioms AQuotientKernelBridge.ofRange

section SubmonoidToSubgroup
variable {G : Type} [Group G]

noncomputable def submonoidToSubgroup (H : Subgroup G) :
    H.toSubmonoid ≃* H where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end SubmonoidToSubgroup

noncomputable def AQuotientKernelBridge.ofRangeKernel
    (h : CommGroup.torsion Fˣ ≤ (unitValuationHom (F := F)).ker) :
    ((unitValuationHom (F := F)).ker ⧸
        (CommGroup.torsion Fˣ).comap
          (Subgroup.subtype (unitValuationHom (F := F)).ker)) ≃*
      (quotientValuationHom (F := F) h).ker :=
  (AQuotientKernelBridge.ofRange (F := F) h).equiv.trans
    (submonoidToSubgroup (quotientValuationHom (F := F) h).ker)

#print axioms AQuotientKernelBridge.ofRangeKernel
#print axioms submonoidToSubgroup

end LeanFormal.IUT.XiFPaper.Mzk1Ind1KernelBridgeActual