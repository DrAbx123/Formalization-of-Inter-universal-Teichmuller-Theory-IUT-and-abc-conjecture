import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual

/-! # Native global q-pilot normalized log-volume

Constructs the native global q-pilot normalized log-volume directly on the
actual native bad family Bad (nativePlaceSelection T), with no appeal to any
equivalence I.initial.badPlaces ≃ Bad (nativePlaceSelection T).

Actual inputs:

* nativeBadToFPlace T b : actual finite F-place above the bad moduli place b;
* nativeBadLocalWeight T b = 1/[K_{w_b} : (F_mod)_{v_b}]
  (Remark 3.1.1(ii) local normalized weight, from VbadPlaceIndexingActual);
* the actual F_l^x label group ProcessionLabel l = (ZMod l.value)^x and the
  actual F_l^x procession average from ProcessionNormalizationWeightsActual.

The q-pilot is fixed by F_l^x, so its label function at b is the constant
|log q_b|; the F_l^x average is proved equal to |log q_b|.  The candidate is

  sum_b (1/[K_{w_b}:(F_mod)_{v_b}]) * |log q_b|.

This is not the raw SignedLabel sum and not the uniform canonical procession.
No I.initial badPlaces bridge is constructed.  No fake inequality/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

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

/-- The actual q-pilot local normalized weight at the F-place over a native bad
place: 1/[K_{w_b}:(F_mod)_{v_b}] by Remark 3.1.1(ii). -/
noncomputable def nativeQPilotLocalNormalizedWeight
    (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b

/-- Exact actual formula for the native local normalized weight. -/
theorem nativeQPilotLocalNormalizedWeight_eq
    (b : Bad (nativePlaceSelection T)) :
    nativeQPilotLocalNormalizedWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  rfl

/-- The q-pilot label function is constant on the F_l^x procession (the q-pilot
is fixed by the F_l^x action). -/
noncomputable def nativeQPilotLabelLogMagnitude
    (b : Bad (nativePlaceSelection T)) (j : ProcessionLabel l) : Real :=
  baseQLogMagnitude T b

/-- The actual F_l^x procession average of the q-pilot label function. -/
noncomputable def nativeQPilotFLAverageLogMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  processionAverage l (nativeQPilotLabelLogMagnitude T b)

/-- The actual F_l^x average of the constant q-pilot label function equals the
base q log-magnitude. -/
theorem nativeQPilotFLAverageLogMagnitude_eq
    (b : Bad (nativePlaceSelection T)) :
    nativeQPilotFLAverageLogMagnitude T b = baseQLogMagnitude T b := by
  unfold nativeQPilotFLAverageLogMagnitude nativeQPilotLabelLogMagnitude
  rw [processionAverage_eq_sum_div]
  haveI : Nonempty (ProcessionLabel l) := ⟨1⟩
  have hcard : (Fintype.card (ProcessionLabel l) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ProcessionLabel l))
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [hcard]

/-- Actual local paper q-pilot normalized log-magnitude: weight times F_l^x
average. -/
noncomputable def nativeQPilotLocalNormalizedLogMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  nativeQPilotLocalNormalizedWeight T b *
    nativeQPilotFLAverageLogMagnitude T b

/-- Actual formula for the local normalized magnitude. -/
theorem nativeQPilotLocalNormalizedLogMagnitude_eq
    (b : Bad (nativePlaceSelection T)) :
    nativeQPilotLocalNormalizedLogMagnitude T b =
      nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold nativeQPilotLocalNormalizedLogMagnitude nativeQPilotLocalNormalizedWeight
  rw [nativeQPilotFLAverageLogMagnitude_eq]

/-- The actual native global q-pilot normalized log-magnitude (Remark 3.1.1
weights). -/
noncomputable def nativeGlobalQPilotNormalizedLogMagnitude : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeQPilotLocalNormalizedLogMagnitude T b

/-- Exact formula for the native global normalized magnitude. -/
theorem nativeGlobalQPilotNormalizedLogMagnitude_eq :
    nativeGlobalQPilotNormalizedLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * baseQLogMagnitude T b := by
  unfold nativeGlobalQPilotNormalizedLogMagnitude
  apply Finset.sum_congr rfl
  intro b _
  exact nativeQPilotLocalNormalizedLogMagnitude_eq T b

/-- The actual native global q-pilot normalized signed log-volume. -/
noncomputable def nativeGlobalQPilotNormalizedSignedLogVolume : Real :=
  -nativeGlobalQPilotNormalizedLogMagnitude T

end LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

end
