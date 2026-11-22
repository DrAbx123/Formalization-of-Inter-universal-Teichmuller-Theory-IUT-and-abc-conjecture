/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6KviPlaceActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
variable {l : PrimeGeFive} (X : N8NativeInput l)
abbrev KviAtF : Type := Completion (K := X.S.arithmetic.F) (nativeFPlaceOverBad X)
instance KviAtF_field : Field (KviAtF X) := inferInstance
theorem Kvi_place_same_source :
    comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) = nativeBadBasePlace X :=
  nativeFPlaceOverBad_comap X
theorem Kvi_place_mem_bad :
    comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) ∈ X.S.tuple.source.V_mod_bad :=
  nativeFPlaceOverBad_mem_bad X
#print axioms Kvi_place_same_source
#print axioms Kvi_place_mem_bad
end LeanFormal.IUT.XiFPaper.Mzk1P6KviPlaceActual
