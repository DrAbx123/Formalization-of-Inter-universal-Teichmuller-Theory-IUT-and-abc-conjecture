/- Final P8 uniform-height input shape: the additive height bound, equivalent
to ABC; the producer record implies it. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVInequalityActual
import tmp.sheaf.xif.paper.P8ProducerRecordDone
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8UniformHeightInputFinal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVInequalityActual
open LeanFormal.IUT.XiFPaper.P8ProducerRecordDone

abbrev P8UniformHeightInputFinal : Prop := P8P6IVInequalityInput
theorem inputFinal_iff_ABC : P8UniformHeightInputFinal ↔ ABCConjecture :=
  (LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound).symm
theorem inputFinal_of_ABC (h : ABCConjecture) : P8UniformHeightInputFinal :=
  (LeanFormal.IUT.abcConjecture_iff_abcArithmeticWeightHeightBound).mp h
theorem producer_to_inputFinal (P : P8ProducerRecordDone) :
    P8UniformHeightInputFinal :=
  inputFinal_of_ABC (record_ABCConjecture P)
#print axioms inputFinal_iff_ABC
#print axioms producer_to_inputFinal
end LeanFormal.IUT.XiFPaper.P8UniformHeightInputFinal
end
