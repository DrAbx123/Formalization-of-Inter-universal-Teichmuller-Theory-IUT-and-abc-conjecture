import tmp.sheaf.xif.paper.S889CompatibilityScalingGroupoid
import tmp.sheaf.xif.paper.S872OtriLogVolumeInterfaceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S891IndScaleOneEdgesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S889CompatibilityScalingGroupoid
open LeanFormal.IUT.XiFPaper.S872OtriLogVolumeInterfaceActual

universe u
variable {α : Type}
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual/conditional Ind1/Ind2/Ind3 invariance: each transformation fixes the
paper log-volume. -/
structure IndInvarianceData (α : Type) where
  logVolume : α → Real
  ind1 : α → α
  ind2 : α → α
  ind3 : α → α
  ind1_fixed : ∀ x, logVolume (ind1 x) = logVolume x
  ind2_fixed : ∀ x, logVolume (ind2 x) = logVolume x
  ind3_fixed : ∀ x, logVolume (ind3 x) = logVolume x

/-- Ind edges: one edge for each of Ind1/2/3. -/
inductive IndEdge (D : IndInvarianceData α) (a b : α) : Type
  | ind1 (h : b = D.ind1 a) : IndEdge D a b
  | ind2 (h : b = D.ind2 a) : IndEdge D a b
  | ind3 (h : b = D.ind3 a) : IndEdge D a b

/-- Scale-one compatibility graph for Ind1/2/3. -/
noncomputable def indScaleOneGraph (D : IndInvarianceData α) : ScalingGraph where
  Obj := α
  Edge a b := IndEdge D a b
  step _ := 1
  logVolume := D.logVolume
  edge_law := by
    intro a b e
    cases e with
    | ind1 h =>
        subst h
        simp [D.ind1_fixed a]
    | ind2 h =>
        subst h
        simp [D.ind2_fixed a]
    | ind3 h =>
        subst h
        simp [D.ind3_fixed a]

/-- All Ind edges have scale one. -/
theorem indScaleOneGraph_step_eq_one (D : IndInvarianceData α)
    {a b : α} (e : (indScaleOneGraph D).Edge a b) :
    (indScaleOneGraph D).step e = 1 := rfl

/-- Along any Ind path, log-volume is constant. -/
theorem indPath_logVolume_eq (D : IndInvarianceData α)
    {a b : α} (p : (indScaleOneGraph D).Path a b) :
    D.logVolume a = D.logVolume b :=
  ScalingGraph.Path.logVolume_eq_of_scale_one (indScaleOneGraph D)
    (fun e => indScaleOneGraph_step_eq_one D e) p

/-- qPilot/Theta branch graph: both branches are the same paper lambda-O log,
so the branch swap is a scale-one Ind edge. -/
def qPilotThetaBranchData : IndInvarianceData Bool where
  logVolume bool :=
    if bool then (paperOtriLogVolumeInterface (l := l) T b).hullLog
    else (paperOtriLogVolumeInterface (l := l) T b).qPilotLog
  ind1 := Equiv.swap false true
  ind2 := Equiv.swap false true
  ind3 := Equiv.swap false true
  ind1_fixed := by
    intro x
    cases x <;> rfl
  ind2_fixed := by
    intro x
    cases x <;> rfl
  ind3_fixed := by
    intro x
    cases x <;> rfl

end LeanFormal.IUT.XiFPaper.S891IndScaleOneEdgesActual

end
