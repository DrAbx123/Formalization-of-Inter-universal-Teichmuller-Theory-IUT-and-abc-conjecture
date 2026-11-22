import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier

/-! # Paper line-bundle carrier (base structure)

Pole-allowing carrier for line-bundle sections: localizations land in completion
fields, not in completion integer rings. This base file contains only the
carrier structure, so the paper q-pilot object does not depend on a native
q-pilot line-bundle construction. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

/-- Pole-allowing line-bundle carrier: sections and localizations into
completion fields. -/
structure PaperLineBundleCarrier (k : Type u) [Field k] [NumberField k] where
  total : Type u
  localization : (v : NumberField.FinitePlace k) → total → NumberFieldFinitePlace.Completion v

end LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

end
