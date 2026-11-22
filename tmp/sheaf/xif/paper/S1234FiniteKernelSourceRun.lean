import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceOutputPrimeStripInterpretation
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteParameterized

/-! # S1234: actual finite-kernel SourceRun instance -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1234FiniteKernelSourceRun

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring
open LeanFormal.IUT.SourceFiniteParameterized
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.Theorem311.Output

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

abbrev L (l : PrimeGeFive) : Type := Multiplicative (finiteLabel l)

abbrev C : SourceFiniteParameterized.Carrier l :=
  SourceFiniteParameterized.carrier l

noncomputable abbrev autom :
    SourceProcessionAutomorphismData (SourceFiniteParameterized.carrier l) (L l) :=
  finiteKernelProcessionAutomorphism l

noncomputable abbrev ind2 :
    Ind2ActionData (SourceFiniteParameterized.carrier l) (autom (l := l)) (L l) :=
  finiteKernelInd2ActionData l

noncomputable abbrev input :
    AlgorithmInput (SourceFiniteParameterized.carrier l) :=
  AlgorithmInput.empty (SourceFiniteParameterized.carrier l)

noncomputable def finiteKernelRun :
    SourceRun (I := I) (n := 0)
      (C := SourceFiniteParameterized.carrier l) (autom (l := l)) (ind2 (l := l)) (input (l := l)) :=
  sourceRun (I := I) (n := 0)
    (C := SourceFiniteParameterized.carrier l) (autom (l := l)) (ind2 (l := l)) (input (l := l))

theorem finiteKernelRun_forget :
    forgetRun (I := I) (n := 0)
      (C := SourceFiniteParameterized.carrier l) (autom (l := l)) (ind2 (l := l)) (input (l := l)) =
    (runAlgorithm (SourceFiniteParameterized.carrier l) (input (l := l))).target :=
  forgetRun_eq_runAlgorithm_target (I := I) (n := 0)
    (C := SourceFiniteParameterized.carrier l) (autom (l := l)) (ind2 (l := l)) (input (l := l))

end LeanFormal.IUT.XiFPaper.S1234FiniteKernelSourceRun

end
