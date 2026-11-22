/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaLinkSymmetryActual

/-! # Chain: theta-link data compose (monoid-equivalence composition) -/

namespace LeanFormal.IUT.XiFPaper.ThetaLinkSymmetryActual

variable (U V W : Type*) [CommMonoid U] [CommMonoid V] [CommMonoid W]

def tlComp (D : ThetaLinkData U V) (E : ThetaLinkData V W) : ThetaLinkData U W :=
  ⟨D.unitEquiv.trans E.unitEquiv⟩

@[simp] theorem tlComp_unitEquiv (D : ThetaLinkData U V) (E : ThetaLinkData V W) :
    (tlComp U V W D E).unitEquiv = D.unitEquiv.trans E.unitEquiv := rfl

theorem tlComp_apply (D : ThetaLinkData U V) (E : ThetaLinkData V W) (x : U) :
    (tlComp U V W D E).unitEquiv x = E.unitEquiv (D.unitEquiv x) := rfl

theorem tlComp_id_left (D : ThetaLinkData U V) :
    tlComp U U V ⟨MulEquiv.refl U⟩ D = D := by
  cases D
  rfl

theorem tlComp_assoc {X : Type*} [CommMonoid X]
    (D : ThetaLinkData U V) (E : ThetaLinkData V W) (F : ThetaLinkData W X) :
    tlComp U V X D (tlComp V W X E F) = tlComp U W X (tlComp U V W D E) F := by
  cases D
  cases E
  cases F
  rfl

end LeanFormal.IUT.XiFPaper.ThetaLinkSymmetryActual
