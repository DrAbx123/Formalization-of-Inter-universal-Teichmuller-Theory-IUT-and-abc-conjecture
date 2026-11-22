import tmp.sheaf.xif.paper.S2536LocalizedPowersActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
open NumberField
open LeanFormal.IUT.XiFPaper.S2536LocalizedPowersActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace LeanFormal.IUT.XiFPaper.S2555LocalizedIntegralActualAdapted

abbrev C : Type := RingOfIntegers S1720Field
abbrev L : Type := S1720Field

variable (c : ℕ)
abbrev R : Type := Localization (Submonoid.powers c)
abbrev S : Type := Localization (Submonoid.powers (algebraMap ℤ C c))

theorem S2555_isIntegralClosure (hc : c ≠ 0) :
    IsIntegralClosure S L R := by
  haveI : IsIntegralClosure C ℤ L := inferInstance
  haveI : IsFractionRing C L := inferInstance
  exact isIntegralClosure_localization_powers
    (A := ℤ) (C := C) (K := ℚ) (L := L) (R := R) (S := S)
    (a := (c : ℤ)) (ha := mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hc))
    (hACL := inferInstance) (hARS := inferInstance) (hACS := inferInstance)
    (hARL := inferInstance) (hCSL := inferInstance) (hRSL := inferInstance)

#check S2555_isIntegralClosure

end LeanFormal.IUT.XiFPaper.S2555LocalizedIntegralActualAdapted
end
