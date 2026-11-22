/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountUnconditionalActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexRewireActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexGeneratorActual
import Mathlib.Tactic

/-! # P7 #3: B5Index consumer of the unconditional IdealLocalizedCount statement -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexConsumerActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountUnconditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexRewireActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexGeneratorActual

variable {k : Type} [Field k] [NumberField k]

/-- The unconditional localized-count form, restated in B5Index vocabulary. -/
theorem b5Index_localizedCount_consumer
    (I : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0)
    (v : NumberField.FinitePlace k) :
    exists (pi : LocalRing (k := k) v) (e : Nat),
      e = (Associates.mk v.maximalIdeal.asIdeal).count (Associates.mk I).factors ∧
      localizedLine (k := k) (I : LineBundle (k := k)) v =
        Submodule.span (LocalRing (k := k) v)
          {((pi : LocalField (k := k) v) ^ e)} :=
  idealLocalizedCountStatement_proved I hI v

/-- Unconditional rank-one SNF datum together with the localized-count form. -/
theorem b5Index_placeSNFData_and_localizedCount
    (I : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0)
    (v : NumberField.FinitePlace k) :
    Nonempty (PlaceSNFData (k := k) (I : LineBundle (k := k)) v) ∧
      exists (pi : LocalRing (k := k) v) (e : Nat),
        e = (Associates.mk v.maximalIdeal.asIdeal).count (Associates.mk I).factors ∧
        localizedLine (k := k) (I : LineBundle (k := k)) v =
          Submodule.span (LocalRing (k := k) v)
            {((pi : LocalField (k := k) v) ^ e)} :=
  ⟨⟨placeSNFDataActual (k := k) (I : LineBundle (k := k)) v⟩,
    idealLocalizedCountStatement_proved I hI v⟩

/-- The B5Index SNF object remains available (unconditional generator). -/
theorem b5Index_placeSNFData_nonempty
    (I : LineBundle (k := k)) (v : NumberField.FinitePlace k) :
    Nonempty (PlaceSNFData (k := k) I v) :=
  ⟨placeSNFDataActual (k := k) I v⟩

def b5IndexConsumerRows : List (String × String × String) :=
  [ ("b5Index_localizedCount_consumer", "IdealLocalizedCountStatement in B5Index vocabulary", "PROVED"),
    ("b5Index_placeSNFData_and_localizedCount", "SNF datum + localized count", "PROVED"),
    ("b5Index_placeSNFData_nonempty", "unconditional rank-one SNF", "PROVED") ]

theorem b5IndexConsumerRows_length : b5IndexConsumerRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexConsumerActual

end