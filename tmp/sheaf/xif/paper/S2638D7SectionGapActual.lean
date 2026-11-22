import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual

/-! # S2638: D7 section intake — actual D7a and the exact D7b gap -/

noncomputable section
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

namespace LeanFormal.IUT.XiFPaper.S2638D7SectionGapActual

variable (l : PrimeGeFive)

/-- D7a is actual: the canonical place-section layer exists over the paper
arithmetic input A = S1724InitialThetaArithmeticData l. -/
theorem S1727D7aLayerActual :
    Nonempty (SourceValuationSectionLayer (S1727A l)) :=
  SourceValuationSectionLayer.nonempty_canonical (S1727A l)

/-- D7a's canonical layer is exactly `S1727Layer`. -/
theorem S1727D7aLayerActual_eq :
    (SourceValuationSectionLayer.canonical (S1727A l)) = S1727Layer l := rfl

/-- The D7b intake is exactly the D7 local-group supply over the canonical
place-section layer. -/
theorem S1727SectionFirstMissing_def :
    S1727SectionFirstMissing l =
      D7LocalGroupSectionSupply.{0, 0} (S1727Layer l) := rfl

/-- Exact decomposition of the D7b intake into the first field and the tail. -/
theorem S1727D7b_decomp (G : S1727SectionFirstMissing l) :
    (S1727D7SupplyEquiv l G).1 = G.localGroupCarrier ∧
      Nonempty (S1727D7Tail l (S1727D7FirstFieldOfSupply l G)) :=
  ⟨rfl, ⟨(S1727D7SupplyEquiv l G).2⟩⟩

/-- The exact nonemptiness reduction for D7b. -/
theorem S1727D7b_nonempty_iff :
    Nonempty (S1727SectionFirstMissing l) ↔
      ∃ G0 : S1727D7FirstField l, Nonempty (S1727D7Tail l G0) :=
  S1727SectionFirstMissing_nonempty_iff_firstField_tail l

/-- Minimal constructor interface: exactly the curve-side local-group and
place-data input needed by D7b, with no arithmetic or D6 content hidden. -/
structure S1727D7CurveLocalGroupInput where
  localGroupCarrier : (S1727Layer l).valuationCarrier → Type
  modifiedLocalGroupCarrier :
    (S1727Layer l).modifiedValuationCarrier → Type
  localGroupSection : ∀ x, localGroupCarrier x →
    modifiedLocalGroupCarrier ((S1727Layer l).sectionMap x)
  localGroupSection_injective : ∀ x,
    Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x,
    Function.Surjective (localGroupSection x)
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

noncomputable def S1727SectionFirstMissingOfCurveLocalGroupInput
    (I : S1727D7CurveLocalGroupInput l) :
    S1727SectionFirstMissing l where
  localGroupCarrier := I.localGroupCarrier
  modifiedLocalGroupCarrier := I.modifiedLocalGroupCarrier
  localGroupSection := I.localGroupSection
  localGroupSection_injective := I.localGroupSection_injective
  localGroupSection_surjective := I.localGroupSection_surjective
  finitePlaceData := I.finitePlaceData
  finitePlaceData_proved := I.finitePlaceData_proved
  infinitePlaceData := I.infinitePlaceData
  infinitePlaceData_proved := I.infinitePlaceData_proved

#check S1727D7aLayerActual
#check S1727D7b_nonempty_iff
#check S1727SectionFirstMissingOfCurveLocalGroupInput
#print axioms S1727SectionFirstMissingOfCurveLocalGroupInput

end LeanFormal.IUT.XiFPaper.S2638D7SectionGapActual
end
