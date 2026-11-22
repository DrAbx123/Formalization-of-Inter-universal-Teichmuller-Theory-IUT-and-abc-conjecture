import tmp.sheaf.xif.paper.S2603LiftTLInjectiveActual
import tmp.sheaf.xif.paper.S2600TIntegralClosureActual
import tmp.sheaf.xif.paper.S2565ConcreteIntegralClosureCActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2562HZcMonicCActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2605LiftSLActual

abbrev Cb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev Sb : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S
abbrev Fb : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev Lb : Type := LeanFormal.IUT.XiFPaper.S2599TInstancesActual.L

open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

local instance hloc : IsLocalization (Submonoid.powers (Cden : Cb)) Sb := by
  have h := LeanFormal.IUT.XiFPaper.S2600TIntegralClosureActual.N_eq_powers
  rw [← h]
  exact inferInstance

noncomputable def gCL : Cb →+* Lb := algebraMap Cb Lb

lemma algebraMap_Cb_Lb_injective : Function.Injective (algebraMap Cb Lb) := by
  have h1 : Function.Injective (algebraMap Cb Fb) :=
    IsIntegralClosure.algebraMap_injective (A := Cb) (R := ℤ) (B := Fb)
  have h2 : Function.Injective (algebraMap Fb Lb) := FaithfulSMul.algebraMap_injective Fb Lb
  have hcomp : algebraMap Cb Lb = (algebraMap Fb Lb).comp (algebraMap Cb Fb) := by
    ext x
    rfl
  rw [hcomp]
  exact h2.comp h1

lemma Cden_Cb_ne_zero : (Cden : Cb) ≠ 0 := by
  intro h
  exact Cden_ne_zero (by exact_mod_cast h)

lemma gCL_Cden_ne_zero : gCL (Cden : Cb) ≠ 0 := by
  unfold gCL
  simpa using algebraMap_Cb_Lb_injective.ne Cden_Cb_ne_zero

lemma gCL_unit : ∀ y ∈ Submonoid.powers (Cden : Cb), IsUnit (gCL y) := by
  intro y hy
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y (Cden : Cb)).mp hy
  rw [← hn, map_pow]
  exact IsUnit.pow n (isUnit_iff_ne_zero.mpr gCL_Cden_ne_zero)

noncomputable def liftSL : Sb →+* Lb :=
  IsLocalization.lift (M := Submonoid.powers (Cden : Cb)) (g := gCL) (fun y => gCL_unit y.1 y.2)

local instance : Algebra Sb Lb := liftSL.toAlgebra

lemma liftSL_comp : liftSL.comp (algebraMap Cb Sb) = gCL := by
  exact IsLocalization.lift_comp (M := Submonoid.powers (Cden : Cb)) (g := gCL) (fun y => gCL_unit y.1 y.2)


example : (algebraMap Sb Lb) = liftSL := rfl

end LeanFormal.IUT.XiFPaper.S2605LiftSLActual
end