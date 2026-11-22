/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

/-! # Theta-link: consumers for the inverse link (Core) -/

namespace LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open Multiplicative

section Core

variable {U V G H : Type*} [Group U] [Group V] [CommGroup G] [CommGroup H]
variable (u : U →* G) (v : V →* H) (q : G) (theta : H)
variable (degreeG : G →* Multiplicative ℤ) (degreeH : H →* Multiplicative ℤ)
variable (hu : Function.Injective u) (hv : Function.Injective v)
variable (hunitG : ∀ a, degreeG (u a) = 1)
variable (hunitH : ∀ b, degreeH (v b) = 1)
variable (hq : (degreeG q).toAdd ≠ 0)
variable (htheta : (degreeH theta).toAdd ≠ 0)

theorem thetaLinkSymm_apply_apply (e : U ≃* V)
    (x : unitGeneratedSubmonoid u q) :
    thetaLinkSymm u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e x) = x := by
  rw [thetaLinkSymm_apply]
  exact (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).symm_apply_apply x

theorem thetaLink_apply_symm_apply (e : U ≃* V)
    (y : unitGeneratedSubmonoid v theta) :
    thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (thetaLinkSymm u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e y) = y := by
  rw [thetaLinkSymm_apply]
  exact (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).apply_symm_apply y

theorem thetaLinkSymm_generator (e : U ≃* V) :
    thetaLinkSymm u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (distinguishedGenerator v theta) = distinguishedGenerator u q := by
  rw [thetaLinkSymm_apply]
  exact (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).symm_apply_eq.mpr
    (thetaLink_generator u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).symm

theorem thetaLinkSymm_embeddedUnit (e : U ≃* V) (b : V) :
    thetaLinkSymm u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e
        (embeddedUnit v theta b) = embeddedUnit u q (e.symm b) := by
  rw [thetaLinkSymm_apply]
  exact (thetaLink u v q theta degreeG degreeH hu hv hunitG hunitH hq htheta e).symm_apply_eq.mpr
    (by rw [thetaLink_embeddedUnit]; simp)

end Core

end LeanFormal.IUT.IUTII.Theta.ThetaLinkAssembly

