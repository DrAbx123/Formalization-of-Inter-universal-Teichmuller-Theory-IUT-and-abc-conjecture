/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Theta-link: unit-equivalence symmetry data -/

namespace LeanFormal.IUT.XiFPaper.ThetaLinkSymmetryActual

variable (U V : Type*) [CommMonoid U] [CommMonoid V]

structure ThetaLinkData where
  unitEquiv : U ≃* V

def tlSymm (D : ThetaLinkData U V) : ThetaLinkData V U :=
  ⟨D.unitEquiv.symm⟩

theorem tlSymm_symm (D : ThetaLinkData U V) : tlSymm V U (tlSymm U V D) = D := by
  cases D
  rfl

theorem tlSymm_apply (D : ThetaLinkData U V) (x : U) :
    (tlSymm V U (tlSymm U V D)).unitEquiv x = D.unitEquiv x := rfl

end LeanFormal.IUT.XiFPaper.ThetaLinkSymmetryActual
