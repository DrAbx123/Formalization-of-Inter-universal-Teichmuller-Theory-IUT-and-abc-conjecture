import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase
import tmp.sheaf.xif.paper.QPilotPaperLineBundleActual
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.n8.closure.NativeSourceReductionActual

/-! # Actual pole-allowing paper line-bundle carrier

The reduced `SourceArithmeticVectorBundle` localizes into completion *integer*
rings and therefore cannot carry O(-D).  This file builds the actual carrier
whose sections are the fractional-ideal sections and whose localizations land in
the completion field, so poles at bad primes are allowed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.QPilotPaperLineBundleActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Pole-allowing carrier of the q-pilot O(-D) line bundle: sections are
fractional-ideal elements; localization is the actual completion embedding. -/
noncomputable def qPilotLineBundleCarrier :
    (v : NumberField.FinitePlace (QPilotBaseField X)) →
      qPilotLineBundle X → NumberFieldFinitePlace.Completion v :=
  fun v x => algebraMap (QPilotBaseField X) (NumberFieldFinitePlace.Completion v) (x : QPilotBaseField X)

/-- The carrier is the actual fractional-ideal type, not a zero/PUnit carrier. -/
theorem qPilotLineBundleCarrier_apply
    (v : NumberField.FinitePlace (QPilotBaseField X)) (x : qPilotLineBundle X) :
    qPilotLineBundleCarrier X v x =
      algebraMap (QPilotBaseField X) (NumberFieldFinitePlace.Completion v) (x : QPilotBaseField X) :=
  rfl

/-- The q-pilot O(-D) carrier with actual fractional-ideal sections. -/
noncomputable def qPilotPaperLineBundleCarrier :
    PaperLineBundleCarrier (QPilotBaseField X) where
  total := qPilotLineBundle X
  localization := qPilotLineBundleCarrier X

end LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual

end
