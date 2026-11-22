/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Frobenioid.Example36FrobenioidTransport

/-!
# Frobenius transport: global-unit map bookkeeping (IUTII Frobenioid node)

Declaration-level addendum to `Example36FrobenioidTransport`: the induced map on global
units of a ring homomorphism is functorial (composition, identity), injective when the
ring homomorphism is injective, and compatible with the unit power/multiplication
structure.  These are the elementary functoriality facts needed when composing place
localization transport data along a tower of number-field extensions.

SHEAF node: iuti-ii:Frobenioid.UnitsTransport (kind theorem; status PENDING-VERIFY until
the DAG watchdog reports EXIT0).  No new axioms; Mathlib-only proofs.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']
variable {F'' : Type u} [Field F''] [NumberField F'']

/-- The global-unit map is functorial in the ring homomorphism (contravariant order:
`phi.comp psi` gives the composite unit map). -/
theorem unitsMapOfRingHom_comp (phi : F' →+* F'') (psi : F →+* F') :
    unitsMapOfRingHom (phi.comp psi) =
      (unitsMapOfRingHom phi).comp (unitsMapOfRingHom psi) := by
  ext x
  rfl

/-- Pointwise form of the functoriality identity. -/
theorem unitsMapOfRingHom_comp_apply (phi : F' →+* F'') (psi : F →+* F') (f : Fˣ) :
    unitsMapOfRingHom (phi.comp psi) f =
      unitsMapOfRingHom phi (unitsMapOfRingHom psi f) := by
  rfl

/-- An injective ring homomorphism induces an injective map on global units. -/
theorem unitsMapOfRingHom_injective (phi : F →+* F')
    (hphi : Function.Injective phi) : Function.Injective (unitsMapOfRingHom phi) := by
  intro x y hxy
  apply Units.ext
  apply hphi
  have h := congrArg (fun z : F'ˣ => (z : F')) hxy
  simpa using h

/-- The identity ring homomorphism induces the identity map on global units. -/
theorem unitsMapOfRingHom_id_apply (f : Fˣ) :
    unitsMapOfRingHom (RingHom.id F) f = f := by
  exact unitsMapOfRingHom_id f

variable {F''' : Type u} [Field F'''] [NumberField F''']

/-- Composition of three ring homomorphisms: associativity of the induced global-unit maps. -/
theorem unitsMapOfRingHom_comp_assoc (f : F'' →+* F''') (g : F' →+* F'') (h : F →+* F') :
    unitsMapOfRingHom (f.comp (g.comp h)) = unitsMapOfRingHom ((f.comp g).comp h) := by
  ext x
  rfl

/-- The induced unit map commutes with integer powers. -/
theorem unitsMapOfRingHom_zpow (phi : F →+* F') (f : Fˣ) (n : ℤ) :
    unitsMapOfRingHom phi (f ^ n) = unitsMapOfRingHom phi f ^ n := by
  exact map_zpow (unitsMapOfRingHom phi) f n

/-- Equal ring homomorphisms induce equal global-unit maps. -/
theorem unitsMapOfRingHom_congr {phi psi : F →+* F'} (h : phi = psi) :
    unitsMapOfRingHom phi = unitsMapOfRingHom psi := by
  rw [h]

end LeanFormal.IUT.IUTII.Frobenioid.Example36

end