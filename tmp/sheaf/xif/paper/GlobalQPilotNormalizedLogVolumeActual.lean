import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-! # Global q-pilot normalized log-volume candidate

Uses the actual logdescent-interface weights:

* localNormalizedWeight T.arithmetic w = 1/[K_w : (F_mod)_v]
  (ProcessionNormalizationWeightsActual.localNormalizedWeight);
* nativeBadToFPlace T b is the actual finite F-place above the bad place b;
* the actual F_l^x label group ProcessionLabel l = (ZMod l.value)^x and its
  actual procession average.

The q-pilot is fixed by the F_l^x action, so its actual label function is the
constant base-q log-magnitude; the F_l^x average of a constant is proved equal
to that constant.  The paper q-pilot normalized log-volume candidate is then

  sum_b  (1/[K_{w_b}:(F_mod)_{v_b}]) * |log q_b|.

This is not the raw SignedLabel sum and not the uniform canonical procession.
The abstract OriginalInput.badPlaces indexing is not the native Bad index; that
exact bridge is recorded by VbadPlaceIndexingActual.VbadPlaceIndexingObstruction.
A nontrivial Theta action on the q-pilot is also not present; its exact missing
target type is recorded.  No fake inequality/weight/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalQPilotNormalizedLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual paper local normalized weight at the F-place over b:
1/[K_{w_b} : (F_mod)_{v_b}]. -/
noncomputable def qPilotLocalNormalizedWeight
    (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b

/-- The q-pilot is fixed by the F_l^x action, so its actual label function at b
is the constant base q log-magnitude. -/
noncomputable def qPilotLabelLogMagnitude
    (b : Bad (nativePlaceSelection T)) (j : ProcessionLabel l) : Real :=
  baseQLogMagnitude T b

/-- Actual F_l^x procession average of the q-pilot label function. -/
noncomputable def qPilotFLAverageLogMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  processionAverage l (qPilotLabelLogMagnitude T b)

/-- The actual F_l^x average of the constant q-pilot label function is the
base q log-magnitude. -/
theorem qPilotFLAverageLogMagnitude_eq
    (b : Bad (nativePlaceSelection T)) :
    qPilotFLAverageLogMagnitude T b = baseQLogMagnitude T b := by
  unfold qPilotFLAverageLogMagnitude qPilotLabelLogMagnitude
  rw [processionAverage_eq_sum_div]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (ProcessionLabel l) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := ProcessionLabel l)
  field_simp [hcard]
  rw [Finset.card_univ]
  ring

/-- The actual local paper q-pilot normalized log-magnitude:
local normalized weight times the F_l^x-averaged q-pilot log-magnitude. -/
noncomputable def qPilotLocalNormalizedLogMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotLocalNormalizedWeight T b * qPilotFLAverageLogMagnitude T b

/-- Actual formula for the local normalized magnitude. -/
theorem qPilotLocalNormalizedLogMagnitude_eq
    (b : Bad (nativePlaceSelection T)) :
    qPilotLocalNormalizedLogMagnitude T b =
      nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold qPilotLocalNormalizedLogMagnitude qPilotLocalNormalizedWeight
  rw [qPilotFLAverageLogMagnitude_eq]

/-- The actual global paper q-pilot normalized log-magnitude candidate: sum
over the actual V_bad index of the local normalized magnitudes. -/
noncomputable def paperQPilotNormalizedLogMagnitude : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    qPilotLocalNormalizedLogMagnitude T b

/-- Actual formula for the global candidate. -/
theorem paperQPilotNormalizedLogMagnitude_eq :
    paperQPilotNormalizedLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold paperQPilotNormalizedLogMagnitude
  apply Finset.sum_congr rfl
  intro b _
  exact qPilotLocalNormalizedLogMagnitude_eq T b

/-- The actual paper q-pilot normalized signed log-volume. -/
noncomputable def paperQPilotNormalizedSignedLogVolume : Real :=
  -paperQPilotNormalizedLogMagnitude T

/-- The local normalized weight is positive. -/
theorem qPilotLocalNormalizedWeight_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < qPilotLocalNormalizedWeight T b := by
  unfold qPilotLocalNormalizedWeight nativeBadLocalWeight
  rw [localNormalizedWeight_eq_inv]
  apply inv_pos.mpr
  have hdeg : 1 <= localCompletionDegree T.arithmetic (nativeBadToKPlace T b) := by
    unfold localCompletionDegree
    exact one_le_finrank_adicCompletion (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)
  exact_mod_cast hdeg

/-- Each actual local normalized magnitude is positive. -/
theorem qPilotLocalNormalizedLogMagnitude_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < qPilotLocalNormalizedLogMagnitude T b := by
  rw [qPilotLocalNormalizedLogMagnitude_eq]
  exact mul_pos (qPilotLocalNormalizedWeight_pos T b) (baseQLogMagnitude_pos T b)

/-- The global normalized magnitude is positive when V_bad is nonempty. -/
theorem paperQPilotNormalizedLogMagnitude_pos
    [Nonempty (Bad (nativePlaceSelection T))] :
    0 < paperQPilotNormalizedLogMagnitude T := by
  unfold paperQPilotNormalizedLogMagnitude
  exact Finset.sum_pos
    (fun b _ => qPilotLocalNormalizedLogMagnitude_pos T b)
    Finset.univ_nonempty

/-- Exact missing abstraction bridge: the abstract OriginalInput.badPlaces are
not identified with the native Bad index. -/
def AbstractVbadIndexingObstruction
    {V : Type} (I : LeanFormal.IUT.Theorem311Source.OriginalInput l V) : Prop :=
  VbadPlaceIndexingActual.VbadPlaceIndexingObstruction (l := l) I T

/-- Exact missing nontrivial Theta action on the q-pilot object.  The q-pilot is
fixed by F_l^x in the paper; any nontrivial Theta action beyond the constant
label function used above is not present in the frozen tree. -/
structure NontrivialThetaActionOnQPilotTarget : Type

/-- Exact obstruction for the nontrivial Theta action. -/
def NontrivialThetaActionOnQPilotObstruction : Prop :=
  Nonempty (NontrivialThetaActionOnQPilotTarget)

end LeanFormal.IUT.XiFPaper.GlobalQPilotNormalizedLogVolumeActual

end
