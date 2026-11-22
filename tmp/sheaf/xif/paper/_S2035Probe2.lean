import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import Mathlib.FieldTheory.KrullTopology

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

namespace S2035Probe2

variable (v : FinitePrimePlace 2 7)
local instance : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩

abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace ℚ :=
  finitePrimePlaceToQ v

-- The completion at QPlace v is definitionally the adicCompletion at the rational prime.
example : Completion (QPlace v) = (rationalHeightOneSpectrum v.1).adicCompletion ℚ := rfl

noncomputable def completionPadicEquiv :
    ℚ_[v.1] ≃+* Completion (QPlace v) :=
  (rationalFinitePlacePadicEquiv v.1).toRingEquiv

noncomputable def eAlgClosure :
    AlgebraicClosure ℚ_[v.1] ≃+* SourceAlgebraicClosure (QPlace v) :=
  IsAlgClosure.equivOfEquiv (L := AlgebraicClosure ℚ_[v.1])
    (M := SourceAlgebraicClosure (QPlace v))
    (S := ℚ_[v.1]) (R := Completion (QPlace v))
    (completionPadicEquiv v)

example (x : ℚ_[v.1]) :
    eAlgClosure v (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) x) =
      algebraMap (Completion (QPlace v)) (SourceAlgebraicClosure (QPlace v))
        (completionPadicEquiv v x) := by
  exact IsAlgClosure.equivOfEquiv_algebraMap _ _ _ x

end S2035Probe2
