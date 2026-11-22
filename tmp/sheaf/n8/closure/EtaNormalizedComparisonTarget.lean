import tmp.sheaf.n8.closure.EtaQVolumeIndexComparison

/-!
# Corrected normalized eta comparison target

The raw equality etaSelectedLogVolume = etaPilotQ is false.  The actual relation
is a strict comparison determined by the production volume index:

- if volumeIndex = 1, the selected log-volume is 0 and is strictly below q;
- if 2 <= volumeIndex, then log(2) <= log(volumeIndex), while q < log 2, so q is
  strictly below the selected log-volume.

This is a corrected comparison using the actual volume index (the production
LogShellVolumeConsumer index) and the actual q normalization; no arbitrary
normalization factor or equality is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNormalizedComparisonTargetRoute

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaSelectedPlaceReadoutRoute
open LeanFormal.IUT.N8Closure.EtaQVolumeIndexComparison
open LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Actual production volume index at the selected place. -/
def etaSelectedVolumeIndex (X : N8NativeInput l) : Nat :=
  (etaIntegralStructureAtSelectedPlace X).volume.index

/-- Corrected normalized comparison: the exact relative order depends on the
actual volume index being 1 or at least 2. -/
def EtaNormalizedComparisonTarget (X : N8NativeInput l) : Prop :=
  (etaSelectedVolumeIndex X = 1 ∧
      etaSelectedLogVolume X < etaPilotQ X) ∨
    (2 ≤ etaSelectedVolumeIndex X ∧
      etaPilotQ X < etaSelectedLogVolume X)

/-- Actual corrected comparison; every native X satisfies one of the two
branches, with the branch determined by the production volume index. -/
theorem etaNormalizedComparison_actual (X : N8NativeInput l) :
    EtaNormalizedComparisonTarget X := by
  have hidxpos : 0 < etaSelectedVolumeIndex X :=
    (etaIntegralStructureAtSelectedPlace X).volume.index_pos
  rcases Nat.lt_or_ge 1 (etaSelectedVolumeIndex X) with hlt | hge
  · -- 1 >= index, hence index = 1
    have hidx : etaSelectedVolumeIndex X = 1 := by omega
    left
    refine ⟨hidx, ?_⟩
    have hlog : etaSelectedLogVolume X = 0 := by
      rw [etaSelectedLogVolume_eq_log_index]
      change Real.log (((etaSelectedVolumeIndex X : Nat)) : Real) = 0
      rw [hidx]
      norm_num
    rw [hlog]
    exact etaPilotQ_pos X
  · -- 1 < index, hence 2 <= index
    have h2 : 2 ≤ etaSelectedVolumeIndex X := by omega
    right
    refine ⟨h2, ?_⟩
    have hlog2le : Real.log 2 ≤ etaSelectedLogVolume X := by
      rw [etaSelectedLogVolume_eq_log_index]
      change Real.log 2 ≤ Real.log (((etaSelectedVolumeIndex X : Nat)) : Real)
      exact Real.log_le_log (by norm_num : (0 : Real) < 2) (by exact_mod_cast h2)
    exact lt_of_lt_of_le (etaPilotQ_lt_log_two X) hlog2le

/-- The corrected comparison is incompatible with the raw equality. -/
theorem etaNormalizedComparison_not_rawGap
    (X : N8NativeInput l) :
    ¬ EtaSelectedPlaceQPilotGap X :=
  etaSelectedPlaceQPilotGap_false X

end LeanFormal.IUT.N8Closure.EtaNormalizedComparisonTargetRoute
