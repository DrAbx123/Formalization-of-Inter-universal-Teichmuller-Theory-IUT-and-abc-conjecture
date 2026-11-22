import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace LeanFormal.IUT

universe u

theorem SourceLogShellDatum.descends_iff
    (D : SourceLogShellDatum) {Y : Type u}
    (f : D.Units → Y) :
    (∃ fbar : D.logMap.range → Y,
      ∀ u : D.Units,
        fbar ⟨D.logMap u, ⟨u, rfl⟩⟩ = f u) ↔
    (∀ (u t : D.Units), t ∈ D.logMap.ker → f (t * u) = f u) := by
  constructor
  · rintro ⟨fbar, hfbar⟩ u t ht
    have hlog : D.logMap (t * u) = D.logMap u := by
      rw [map_mul, MonoidHom.mem_ker.mp ht, one_mul]
    have hsub :
        (⟨D.logMap (t * u), ⟨t * u, rfl⟩⟩ : D.logMap.range) =
          ⟨D.logMap u, ⟨u, rfl⟩⟩ :=
      Subtype.ext hlog
    rw [← hfbar (t * u), hsub, hfbar u]
  · intro hf
    let q : D.Units ⧸ D.logMap.ker → Y :=
      Quotient.lift f (by
        intro a b hab
        have hab' : QuotientGroup.leftRel D.logMap.ker a b := hab
        have hker : a⁻¹ * b ∈ D.logMap.ker :=
          QuotientGroup.leftRel_apply.mp hab'
        have h1 : f ((a⁻¹ * b) * a) = f a := hf a (a⁻¹ * b) hker
        have hmul : (a⁻¹ * b) * a = b := by
          rw [mul_comm (a⁻¹ * b) a, mul_inv_cancel_left]
        rw [hmul] at h1
        exact h1.symm)
    let e := QuotientGroup.quotientKerEquivRange D.logMap
    refine ⟨fun y => q (e.symm y), ?_⟩
    intro u
    have hmem : D.logMap u ∈ D.logMap.range := MonoidHom.mem_range.mpr ⟨u, rfl⟩
    have htarget : e (QuotientGroup.mk u) = ⟨D.logMap u, hmem⟩ := rfl
    have hsymm : e.symm ⟨D.logMap u, hmem⟩ = QuotientGroup.mk u := by
      rw [← htarget]
      exact e.symm_apply_apply (QuotientGroup.mk u)
    change q (e.symm ⟨D.logMap u, hmem⟩) = f u
    rw [hsymm]
    rfl

end LeanFormal.IUT
