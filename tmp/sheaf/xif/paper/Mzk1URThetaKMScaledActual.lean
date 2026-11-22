/- C2 M-scale calibration (kurt): carry the 1/(2l) scalar through the C2 chain.

The accepted sandwich gives -Q <= theta (Q = actualQPilotMagnitudeClassical, q-scale). Dividing
by 2l > 0 gives the M-scale C2 lower bound -M <= theta_M with M := Q/(2l) and
theta_M := actualThetaHullLogRoot/(2l). This is the option (b) route: the theta side of C2 is
read at M scale, matching the route q_P5 = -M. No new conditions, no fake.

Default heartbeats.
-/
import tmp.sheaf.xif.paper.Mzk1P6HCor312SandwichChain
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKMScaledActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SandwichChain

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Route M := Q/(2l) at the actual Q. -/
noncomputable def actualQM : ℝ :=
  actualQPilotMagnitudeClassical (l := l) T / (2 * (l.value : ℝ))

/-- M-scale actual theta readout: theta/(2l). -/
noncomputable def actualThetaHullLogRootM : ℝ :=
  actualThetaHullLogRoot (l := l) T / (2 * (l.value : ℝ))

/-- M-scale C2 lower bound: -M <= theta_M (via the accepted -Q <= theta sandwich). -/
theorem neg_actualQM_le_thetaM : -actualQM (l := l) T ≤ actualThetaHullLogRootM (l := l) T := by
  have h := Mzk1P6HCor312SandwichChain.p6SandwichChain_neg_M_le_HTheta (l := l) T
  have hpos : (0 : ℝ) < 2 * (l.value : ℝ) := by positivity
  have h2 := div_le_div_of_nonneg_right h hpos.le
  unfold actualQM actualThetaHullLogRootM
  exact h2

/-- The six-slot constant form of the lower bound. -/
theorem neg_actualQM_le_thetaM' :
    -(actualQPilotMagnitudeClassical (l := l) T) / (2 * (l.value : ℝ)) ≤
      actualThetaHullLogRoot (l := l) T / (2 * (l.value : ℝ)) :=
  neg_actualQM_le_thetaM (l := l) T

#print axioms neg_actualQM_le_thetaM
#print axioms neg_actualQM_le_thetaM'

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKMScaledActual
end