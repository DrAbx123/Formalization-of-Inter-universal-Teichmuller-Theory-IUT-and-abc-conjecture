import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.PaperQPilotObject

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2681HcompBadQAlignmentActual

universe ua uv upi umon ui
variable {l : PrimeGeFive}
variable {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)

noncomputable def S2681NativeBaseQGlobalMagnitude
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  baseQTotalLogMagnitude T

def S2681BadQAlignment
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
    ∀ b : I.initial.badPlaces,
      |Real.log (I.initial.reduction.qParameter b)| =
        baseQLogMagnitude T (e b)

theorem S2681SourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude
    [Fintype (Bad (nativePlaceSelection T))]
    (h : S2681BadQAlignment (I := I) T) :
    sourceBadQAbsLog I.initial = S2681NativeBaseQGlobalMagnitude T := by
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  obtain ⟨e, he⟩ := h
  unfold sourceBadQAbsLog S2681NativeBaseQGlobalMagnitude
    baseQTotalLogMagnitude
  calc
    (∑ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)|) =
        ∑ b : I.initial.badPlaces, baseQLogMagnitude T (e b) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      exact he b
    _ = ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
      exact Fintype.sum_equiv e (fun b => baseQLogMagnitude T (e b))
        (fun b => baseQLogMagnitude T b) (fun b => rfl)

def S2681BadQAlignmentRequired
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  S2681BadQAlignment (I := I) T

#print axioms S2681SourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude

end LeanFormal.IUT.XiFPaper.S2681HcompBadQAlignmentActual
end
