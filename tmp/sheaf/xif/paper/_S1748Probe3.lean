import Mathlib.RingTheory.Etale.Finite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.RingTheory.Etale.Field

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace S1748Dbg

variable (K : Type u) [Field K]
abbrev C : Type (u + 1) := (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ
variable {K}
abbrev fiber (Ω : Type u) [Field Ω] [Algebra K Ω] : C K ⥤ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.fiber K Ω
variable (Ω : Type u) [Field Ω] [Algebra K Ω]

def postcompNat (h : Ω ≃ₐ[K] Ω) : fiber (K := K) Ω ⟶ fiber (K := K) Ω where
  app A := FintypeCat.homMk fun f => h.toAlgHom.comp f
  naturality {A B} φ := by
    ext f
    rfl

#check @postcompNat
#check @fiber

end S1748Dbg
