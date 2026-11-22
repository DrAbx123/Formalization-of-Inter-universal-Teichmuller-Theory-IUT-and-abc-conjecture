import tmp.sheaf.xif.paper.Mzk1ActualReadingTargetActual
import tmp.sheaf.xif.paper.Mzk1KappaLemmaActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichChain
universe u v
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [hMeas : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [hBorel : ∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {V : Type} (I : OriginalInput l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
include T hMeas hBorel
/-- Paper `M = Q/(2l)`. -/
noncomputable def p6SandwichChainM (logQ : Real) : Real := logQ / (2 * (l.value : Real))
theorem p6SandwichChainM_eq_AL (logQ : Real) :
    p6SandwichChainM (l := l) logQ = AL (l.value : Real) logQ := rfl
/-- P5 lower half: `-M ≤ H_theta`. -/
theorem p6SandwichChain_neg_M_le_HTheta :
    -actualQPilotMagnitudeClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T := by
  simpa [actualQPilotSignedLogClassical] using actualTargetSigned_actual (l := l) T
/-- P6 upper half plus lower half: actual Cor 3.12 sandwich. -/
theorem p6_sandwichChain_hCor312
    (hP6 : actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3) :
    actualQPilotSignedLogClassical (l := l) T ≤ thetaPilotHullLogVolumeReal C3 :=
  le_trans (p6SandwichChain_neg_M_le_HTheta (l := l) T) hP6
#print axioms p6_sandwichChain_hCor312
end LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichChain
end