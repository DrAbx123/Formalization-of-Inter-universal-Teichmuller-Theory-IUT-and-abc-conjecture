/- P8 actual global constant / Frey criterion assembly: actual S1 isogeny
height data, actual G1 Fermat cover, actual P6 display producers, and the
existing Frey-J criterion equivalence.  The uniform height bound remains the
criterion premise (not proved here); the final criterion equivalence is actual. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual
import tmp.sheaf.xif.paper.Mzk1S1IsogenyHeightActual
import tmp.sheaf.xif.paper.Mzk1P6ActualProducersActual
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1S1IsogenyHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

/-- Actual P8 global data: actual S1 archimedean height-magnification data,
actual G1 Fermat cover data, and actual P6 Thm 1.10 display terms. -/
structure P8ActualGlobalData (c : ℝ) where
  isogenyHeight : S1IsogenyHeightData c
  fermatCover : FermatCoverData ℂ
  displayTerms : Thm110DisplayTerms

/-- The actual uniform height criterion (Frey j product form), retaining the
ABC quantifiers: one bound per epsilon, for all positive primitive triples. -/
def P8UniformHeightCriterion : Prop :=
  ABCFreyJProductHeightCriterion

/-- Final P8 criterion equivalence: the actual uniform Frey j-height bound is
equivalent to the ABC conjecture. -/
theorem p8_finalCriterion :
    P8UniformHeightCriterion ↔ ABCConjecture :=
  (abcConjecture_iff_freyJProductHeightCriterion).symm

/-- Final P8 consumer: a uniform Frey j-height bound yields ABC. -/
theorem p8_abc_of_uniformHeightBound
    (h : P8UniformHeightCriterion) : ABCConjecture :=
  p8_finalCriterion.mp h

/-- The same final criterion packaged with the actual P8 global data. -/
theorem p8_abc_of_actualData
    (D : P8ActualGlobalData c) (h : P8UniformHeightCriterion) : ABCConjecture :=
  p8_abc_of_uniformHeightBound h

#check p8_finalCriterion
#check p8_abc_of_uniformHeightBound
#check p8_abc_of_actualData

end LeanFormal.IUT.XiFPaper.Mzk1P8GlobalFreyCriterionActual
end
