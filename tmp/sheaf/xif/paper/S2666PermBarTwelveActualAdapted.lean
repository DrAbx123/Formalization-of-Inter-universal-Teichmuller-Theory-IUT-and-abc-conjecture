import tmp.sheaf.xif.paper.S2664P10MaxActual
import tmp.sheaf.xif.paper.S2665P10FintypeActual
import tmp.sheaf.xif.paper.S2577Away10FbarActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2666PermBarTwelveActualAdapted
attribute [local instance] Ideal.Quotient.field

abbrev O0 : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev R0 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R

theorem p10_eq_ker (W : LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual.S2584PrimeDegreeOneWitness) :
    LeanFormal.IUT.XiFPaper.S2661P10Actual.p10 W =
      RingHom.ker LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.φ10 := by
  apply le_antisymm
  · change W.p.map (algebraMap O0 R0) ≤
      RingHom.ker LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.φ10
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker,
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.φ10_comp_algebraMap]
    simp [LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.g, hx]
  · let ψ : R0 ⧸ (W.p.map (algebraMap O0 R0)) →+* ZMod 613 :=
      Ideal.Quotient.lift _ LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.φ10 ‹_›
    have hψsurj : Function.Surjective ψ := by
      intro y
      obtain ⟨x, rfl⟩ :=
        LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.φ10_surjective y
      exact ⟨Ideal.Quotient.mk _ x, rfl⟩
    haveI : (LeanFormal.IUT.XiFPaper.S2661P10Actual.p10 W).IsMaximal :=
      LeanFormal.IUT.XiFPaper.S2661P10Actual.p10_isMaximal W
    haveI : (W.p.map (algebraMap O0 R0)).IsMaximal := by
      simpa [LeanFormal.IUT.XiFPaper.S2661P10Actual.p10] using
        (inferInstance : (LeanFormal.IUT.XiFPaper.S2661P10Actual.p10 W).IsMaximal)
    haveI : Field (R0 ⧸ (W.p.map (algebraMap O0 R0))) := Ideal.Quotient.field _
    have hψinj : Function.Injective ψ := by
      intro a b hab
      have h0 : ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have hsub : a - b = 0 := by
        by_contra hne
        have hunit : IsUnit (a - b) := isUnit_iff_ne_zero.mpr hne
        have h0unit : IsUnit (ψ (a - b)) := hunit.map ψ
        rw [h0] at h0unit
        exact not_isUnit_zero h0unit
      exact sub_eq_zero.mp hsub
    intro z hz
    have hz' : ψ (Ideal.Quotient.mk _ z) = 0 := by
      simpa [ψ] using hz
    have h0 : Ideal.Quotient.mk (W.p.map (algebraMap O0 R0)) z = 0 :=
      hψinj (by simpa using hz')
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0

#check p10_eq_ker
#print axioms p10_eq_ker

end LeanFormal.IUT.XiFPaper.S2666PermBarTwelveActualAdapted
end
