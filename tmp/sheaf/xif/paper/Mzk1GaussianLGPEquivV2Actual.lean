import Mathlib

/-!
# Mzk1GaussianLGPEquivV2Actual — LGP compatibility as an equivalence relation (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Pointwise equality of theta-functions is an equivalence relation; Setoid construction. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GaussianLGPEquivV2Actual

/-- LGP-compatible theta-functions: pointwise equal. -/
def LGPCompatible {Theta : Type*} (f g : Theta → ℚ) : Prop := ∀ x, f x = g x

/-- Genuine theorem: LGP compatibility is reflexive. -/
theorem lgp_refl {Theta : Type*} (f : Theta → ℚ) : LGPCompatible f f :=
  fun _ => rfl

/-- Genuine theorem: LGP compatibility is symmetric. -/
theorem lgp_symm {Theta : Type*} {f g : Theta → ℚ} (h : LGPCompatible f g) :
    LGPCompatible g f :=
  fun x => (h x).symm

/-- Genuine theorem: LGP compatibility is transitive. -/
theorem lgp_trans {Theta : Type*} {f g h : Theta → ℚ}
    (hfg : LGPCompatible f g) (hgh : LGPCompatible g h) : LGPCompatible f h :=
  fun x => (hfg x).trans (hgh x)

/-- Genuine theorem: pointwise addition of compatible theta-functions. -/
theorem lgp_add {Theta : Type*} {f g f2 g2 : Theta → ℚ}
    (hf : LGPCompatible f f2) (hg : LGPCompatible g g2) :
    LGPCompatible (fun x => f x + g x) (fun x => f2 x + g2 x) := by
  intro x
  change f x + g x = f2 x + g2 x
  rw [hf x, hg x]

/-- LGP compatibility setoid on theta-functions. -/
def lgpSetoid (Theta : Type*) : Setoid (Theta → ℚ) where
  r := LGPCompatible
  iseqv := ⟨lgp_refl, fun h => lgp_symm h, fun h1 h2 => lgp_trans h1 h2⟩

end LeanFormal.IUT.XiFPaper.Mzk1GaussianLGPEquivV2Actual
