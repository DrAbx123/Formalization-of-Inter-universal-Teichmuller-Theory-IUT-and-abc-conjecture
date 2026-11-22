import tmp.sheaf.xif.paper.S2574LocalizedP12Actual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual

noncomputable section
set_option maxHeartbeats 8000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2574LocalizedP12Actual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

namespace LeanFormal.IUT.XiFPaper.S2659LocalizedHQActualAdapted

theorem S2659Psi5Z_model :
    S2132Psi5Z.map (Int.castRingHom ℚ) = C ((2:ℚ)^36) * S2057Psi5Q := by
  rw [show S2057Psi5Q = S1667Curve.preΨ 5 from rfl]
  rw [S1942_preΨ_five]
  unfold S2132Psi5Z
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  ring_nf

noncomputable def S2659c : S1720Field :=
  algebraMap S S1720Field ((((S2574_lead_unit.unit)⁻¹ : Sˣ) : S)) *
    ((2 : S1720Field) ^ 36)

theorem S2659c_ne_zero : S2659c ≠ 0 := by
  unfold S2659c
  apply mul_ne_zero
  · exact map_ne_zero (algebraMap S S1720Field)
      (Units.ne_zero (S2574_lead_unit.unit)⁻¹)
  · exact pow_ne_zero 36 (by norm_num)

theorem S2659S2574P_map :
    S2574P.map (algebraMap S S1720Field) = C ((2:S1720Field)^36) * S2057Psi5F := by
  rw [S2574P, Polynomial.map_map]
  have hcomp : (algebraMap S S1720Field).comp (algebraMap ℤ S) =
      algebraMap ℤ S1720Field := by
    ext x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply ℤ S S1720Field]
  rw [hcomp, S2659Psi5Z_model, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_ofNat]
  rw [S2057Psi5F]
  simp

theorem S2659S2574f_hq :
    S2574f.map (algebraMap S S1720Field) = C S2659c * S2057Psi5F := by
  rw [S2574f, Polynomial.map_mul, Polynomial.map_C, S2659S2574P_map]
  unfold S2659c
  rw [mul_assoc]
  ring

#check S2659S2574f_hq
#print axioms S2659S2574f_hq

end LeanFormal.IUT.XiFPaper.S2659LocalizedHQActualAdapted
end
