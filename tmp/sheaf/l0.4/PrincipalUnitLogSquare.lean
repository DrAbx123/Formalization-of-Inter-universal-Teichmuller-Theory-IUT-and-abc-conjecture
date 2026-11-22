import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogLinkCompatibility

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# Principal-unit log square for the source theater

The principal-unit logarithm of `sourceBaseLocalField`, transported by
`sourceTheaterScalarMap`, is the principal-unit logarithm of the transported
integral unit.  This is the `unitLog_eq_log1p` restatement of the proved
`sourceTheater_unitLog_square`; no new analysis is introduced.
-/

noncomputable section

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

theorem sourceTheater_principalUnitLog_square
    (u : principalUnits (K := sourceBaseLocalField)) :
    sourceTheaterScalarMap (principalUnitLog u) =
      principalUnitLog
        (⟨integralUnitMapOfMapsIntegers sourceTheaterScalarMap
            (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
            (u : (Integers sourceBaseLocalField)ˣ),
          sourceTheaterScalarMap_mem_principalUnits
            (u : (Integers sourceBaseLocalField)ˣ) u.property⟩ :
          principalUnits (K := sourceTheaterLocalField)) := by
  let u' : (Integers sourceTheaterLocalField)ˣ :=
    integralUnitMapOfMapsIntegers sourceTheaterScalarMap
      (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
      (u : (Integers sourceBaseLocalField)ˣ)
  let hu' : u' ∈ principalUnits :=
    sourceTheaterScalarMap_mem_principalUnits
      (u : (Integers sourceBaseLocalField)ˣ) u.property
  have hsrc : principalUnitLog u =
      unitLog (u : (Integers sourceBaseLocalField)ˣ) :=
    (unitLog_eq_log1p (p := concreteRationalPrime)
      (u : (Integers sourceBaseLocalField)ˣ) u.property).symm
  have htgt : principalUnitLog (⟨u', hu'⟩ : principalUnits (K := sourceTheaterLocalField)) =
      unitLog u' :=
    (unitLog_eq_log1p (p := concreteRationalPrime) u' hu').symm
  rw [hsrc, htgt]
  simpa [u'] using
    sourceTheater_unitLog_square (u := (u : (Integers sourceBaseLocalField)ˣ))

end LeanFormal.IUT.IUTII.Frobenioid.Example36

end