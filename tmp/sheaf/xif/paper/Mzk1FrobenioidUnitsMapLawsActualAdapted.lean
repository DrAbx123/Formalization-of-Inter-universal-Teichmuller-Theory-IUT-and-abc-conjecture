/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Frobenioid: units-map composition laws -/

namespace LeanFormal.IUT.XiFPaper.FrobenioidUnitsMapLawsActual

variable {R S T : Type*} [Monoid R] [Monoid S] [Monoid T]

theorem unitsMap_comp (f : S →* T) (g : R →* S) :
    Units.map (f.comp g) = (Units.map f).comp (Units.map g) := by
  ext u
  rfl

theorem unitsMap_id : Units.map (MonoidHom.id R) = MonoidHom.id Rˣ := by
  ext u
  rfl

theorem unitsMap_comp_apply (f : S →* T) (g : R →* S) (u : Rˣ) :
    Units.map (f.comp g) u = Units.map f (Units.map g u) := rfl

theorem unitsMap_coe (f : S →* T) (u : Sˣ) :
    (Units.map f u : T) = f (u : S) := rfl

end LeanFormal.IUT.XiFPaper.FrobenioidUnitsMapLawsActual
