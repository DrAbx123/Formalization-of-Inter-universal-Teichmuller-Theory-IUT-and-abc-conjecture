import tmp.sheaf.xif.paper.S1270NontrivialCapsuleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
noncomputable section
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
namespace Probe
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
open LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
abbrev Lat (vQ : ActualValuation) (v : actualPlace I vQ) : Type ua :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  ↥(integralLogShellLattice (K := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) v) (p := vQ.1))
noncomputable instance (vQ : ActualValuation) (v : actualPlace I vQ) : Module ℤ (Lat I vQ v) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  exact Module.restrictScalars ℤ ℤ_[vQ.1] (Lat I vQ v)
#check LinearEquiv.neg
end Probe
end
