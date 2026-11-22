/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Frobenioid.Example36FrobenioidTransport

/-! # Reuse: monoid-hom corollaries for the global-unit map (tree asset) -/

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']

theorem unitsMapOfRingHom_one' (phi : F →+* F') :
    unitsMapOfRingHom phi 1 = 1 := map_one (unitsMapOfRingHom phi)

theorem unitsMapOfRingHom_mul' (phi : F →+* F') (f g : Fˣ) :
    unitsMapOfRingHom phi (f * g) = unitsMapOfRingHom phi f * unitsMapOfRingHom phi g :=
  map_mul (unitsMapOfRingHom phi) f g

theorem unitsMapOfRingHom_pow' (phi : F →+* F') (f : Fˣ) (n : Nat) :
    unitsMapOfRingHom phi (f ^ n) = unitsMapOfRingHom phi f ^ n :=
  map_pow (unitsMapOfRingHom phi) f n

theorem unitsMapOfRingHom_one_apply (phi : F →+* F') :
    unitsMapOfRingHom phi (1 : Fˣ) = (1 : F'ˣ) := unitsMapOfRingHom_one' phi

theorem unitsMapOfRingHom_mul_apply (phi : F →+* F') (f g : Fˣ) :
    unitsMapOfRingHom phi (f * g) = unitsMapOfRingHom phi f * unitsMapOfRingHom phi g :=
  unitsMapOfRingHom_mul' phi f g

end LeanFormal.IUT.IUTII.Frobenioid.Example36
