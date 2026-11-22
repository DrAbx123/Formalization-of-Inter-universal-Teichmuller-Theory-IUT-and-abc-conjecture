/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FrobeniusUnitsTransportActual

/-! # Reuse: corollaries of the global-unit transport addendum -/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']
variable {F'' : Type u} [Field F''] [NumberField F'']
variable {F''' : Type u} [Field F'''] [NumberField F''']

theorem unitsMapOfRingHom_comp_apply₂ (phi : F'' →+* F''') (psi : F' →+* F'')
    (chi : F →+* F') (f : Fˣ) :
    unitsMapOfRingHom ((phi.comp psi).comp chi) f =
      unitsMapOfRingHom phi (unitsMapOfRingHom psi (unitsMapOfRingHom chi f)) := by
  rw [unitsMapOfRingHom_comp_apply, unitsMapOfRingHom_comp_apply]

theorem unitsMapOfRingHom_comp_injective (phi : F' →+* F'') (psi : F →+* F')
    (hphi : Function.Injective phi) (hpsi : Function.Injective psi) :
    Function.Injective (unitsMapOfRingHom (phi.comp psi)) := by
  rw [unitsMapOfRingHom_comp]
  exact (unitsMapOfRingHom_injective phi hphi).comp
    (unitsMapOfRingHom_injective psi hpsi)

theorem unitsMapOfRingHom_zpow_zero (phi : F →+* F') (f : Fˣ) :
    unitsMapOfRingHom phi (f ^ (0 : ℤ)) = 1 := by
  rw [unitsMapOfRingHom_zpow]
  simp

theorem unitsMapOfRingHom_id_apply₂ (f : Fˣ) :
    unitsMapOfRingHom (RingHom.id F) f = f := unitsMapOfRingHom_id_apply f

theorem unitsMapOfRingHom_congr_comp {phi psi : F' →+* F''} (h : phi = psi)
    (chi : F →+* F') : unitsMapOfRingHom (phi.comp chi) = unitsMapOfRingHom (psi.comp chi) :=
  unitsMapOfRingHom_congr (by rw [h])

end LeanFormal.IUT.IUTII.Frobenioid.Example36
