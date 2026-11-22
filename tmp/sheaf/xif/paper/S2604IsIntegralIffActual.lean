import tmp.sheaf.xif.paper.S2603LiftTLInjectiveActual
import tmp.sheaf.xif.paper.S2565ConcreteIntegralClosureCActual
import Mathlib.RingTheory.Localization.Integral

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2604IsIntegralIffActual

open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2603LiftTLInjectiveActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev Lb : Type := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.L

local instance isLocSb : IsLocalization (Submonoid.powers (Cden : Cb)) Sb := by
  have h := LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual.N_eq_powers
  rw [← h]
  exact inferInstance

lemma exists_T_of_integral {x : Lb} (hx : IsIntegral Sb x) :
    ∃ y : T, algebraMap T Lb y = x := by
  obtain ⟨m, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Submonoid.powers (Cden : Cb)) (R := Cb) (Rₘ := Sb) (S := Lb) x hx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff m.1 (Cden : Cb)).mp m.2
  have hInt : IsIntegral Cb (m.1 • x) := hint
  obtain ⟨y0, hy0⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := OL) (R := Cb) (B := Lb)).mp hInt
  let s : Submonoid.powers (algebraMap Cb OL (Cden : Cb)) :=
    ⟨(algebraMap Cb OL (Cden : Cb)) ^ n,
      (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩
  refine ⟨IsLocalization.mk' T y0 s, ?_⟩
  change IsLocalization.lift (fun y => gOL_unit y.1 y.2) (IsLocalization.mk' T y0 s) = x
  rw [IsLocalization.lift_mk'_spec]
  rw [hy0, Algebra.smul_def]
  congr 1
  rw [← hn]
  change algebraMap Sb Lb ((Cden : Cb) ^ n) = gOL s
  rw [show gOL s = algebraMap OL Lb ((algebraMap Cb OL (Cden : Cb)) ^ n) from rfl]
  rw [map_pow]
  rw [IsScalarTower.algebraMap_apply Cb Sb Lb]
  congr 1
  rw [IsScalarTower.algebraMap_apply Cb OL Lb]
  congr 1
  rw [map_pow]

end LeanFormal.IUT.XiFPaper.S2604IsIntegralIffActual
end