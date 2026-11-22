import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.ThetaHullActual

/-! # Global q-pilot procession-normalized log-volume

IUT III, Corollary 3.12 (iut3.txt lines 10499-10535, pp. 173-174) defines
-|log(q)| as the procession-normalized mono-analytic log-volume of the image of
a q-pilot object.  By IUT III, Definition 3.8, (i) (iut3.txt lines 6731-6768,
pp. 112-113), the q-pilot object is determined by the collection q_v for
v in V_bad.

This file constructs the candidate global q-pilot log-volume from the actual
V_bad-indexed base q family BaseQFamilyActual:

* globalQPilotLogVolume = sum over V_bad of the actual signed local log q_v;
* globalQPilotLogMagnitude = -globalQPilotLogVolume = sum |log q_v|;
* globalQPilotProcessionLogVolume = the actual canonical signed-label
  procession average of the constant q-pilot log-volume family (the q-pilot
  object has one identical copy for each j in F_l^*), proved equal to the
  V_bad total.

No local log(1/5), no comparison to the Theta average, and no fake inequality is
asserted.  The V_bad finiteness is the actual source finiteness input.  No
sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaperThetaHull
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual global q-pilot log-volume from the V_bad collection: the sum of
the actual signed local log q_v. -/
noncomputable def globalQPilotLogVolume : Real :=
  ∑ b : Bad (nativePlaceSelection T), baseQSignedLog T b

/-- The actual global q-pilot log-magnitude is the negative of the signed
V_bad total. -/
noncomputable def globalQPilotLogMagnitude : Real :=
  -globalQPilotLogVolume (T := T)

/-- The global q-pilot log-volume is the actual base q total signed log. -/
theorem globalQPilotLogVolume_eq_totalSignedLog :
    globalQPilotLogVolume T = baseQTotalSignedLog T := rfl

/-- The global q-pilot log-magnitude is the actual total |log q_v| sum. -/
theorem globalQPilotLogMagnitude_eq_totalLogMagnitude :
    globalQPilotLogMagnitude T = baseQTotalLogMagnitude T := by
  unfold globalQPilotLogMagnitude globalQPilotLogVolume
    baseQTotalLogMagnitude
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [baseQSignedLog_eq_neg_logMagnitude]
  ring

/-- The actual procession normalization: average over the actual signed-label
procession (the q-pilot object has one identical copy per j in F_l^*). -/
noncomputable def qPilotProcessionLogVolume : Real :=
  (canonicalProcession (l := l)).average
    (fun _ : SignedLabel l.value => globalQPilotLogVolume T)

/-- Since the procession copies are identical, the procession-normalized
q-pilot log-volume is the V_bad total. -/
theorem qPilotProcessionLogVolume_eq_global :
    qPilotProcessionLogVolume (T := T) = globalQPilotLogVolume T :=
  (canonicalProcession (l := l)).average_const (globalQPilotLogVolume T)

/-- The procession-normalized q-pilot log-magnitude. -/
noncomputable def qPilotProcessionLogMagnitude : Real :=
  -qPilotProcessionLogVolume (T := T)

/-- The procession-normalized magnitude equals the actual V_bad |log q| sum. -/
theorem qPilotProcessionLogMagnitude_eq_totalLogMagnitude :
    qPilotProcessionLogMagnitude (T := T) = baseQTotalLogMagnitude T := by
  unfold qPilotProcessionLogMagnitude
  rw [qPilotProcessionLogVolume_eq_global]
  change globalQPilotLogMagnitude T = baseQTotalLogMagnitude T
  rw [globalQPilotLogMagnitude_eq_totalLogMagnitude]

/-- The procession-normalized q-pilot magnitude is the sum of the actual
pointwise log-magnitudes over V_bad. -/
theorem qPilotProcessionLogMagnitude_eq_sum :
    qPilotProcessionLogMagnitude (T := T) =
      ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
  rw [qPilotProcessionLogMagnitude_eq_totalLogMagnitude]
  rfl

section Nonempty

variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The global q-pilot log-magnitude is positive (each actual |log q_v| is
positive and V_bad is nonempty). -/
theorem globalQPilotLogMagnitude_pos : 0 < globalQPilotLogMagnitude T := by
  rw [globalQPilotLogMagnitude_eq_totalLogMagnitude]
  unfold baseQTotalLogMagnitude
  apply Finset.sum_pos
  · intro b _
    exact baseQLogMagnitude_pos T b
  · exact Finset.univ_nonempty

/-- The procession-normalized q-pilot log-magnitude is positive. -/
theorem qPilotProcessionLogMagnitude_pos : 0 < qPilotProcessionLogMagnitude T := by
  rw [qPilotProcessionLogMagnitude_eq_totalLogMagnitude]
  simpa [globalQPilotLogMagnitude_eq_totalLogMagnitude]
    using globalQPilotLogMagnitude_pos T

end Nonempty

end LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual

end
