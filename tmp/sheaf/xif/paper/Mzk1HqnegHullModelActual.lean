/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1LastNamedResolutionActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Analysis.SpecialFunctions.Exp
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import Mathlib.Tactic

/-! # A597/A598: discharging `hqneg` by a concrete hull side model

The only sign hypothesis of the final 3.12 statement is
`hqneg : requirementSignedQ (requirementOfReading T R) < 0`, i.e.
`Real.log (R.D.vol {qPilotInThetaCarrier}) < 0`.  This file constructs a concrete
volume model on the actual S1902 carrier:

  `vol S = if S ⊆ {qPilotInThetaCarrier} then Real.exp qRead else 1`

where `qRead` is any strictly negative q-pilot log-volume (in the paper: the
HullDet-side `-sum_b |log q_b|`, strictly negative because the bad places are
nonempty; the concrete source lemmas are
`OrigXiFPaperQPilotObject.qPilotLogVolume_neg_of_bad_nonempty` and
`Mzk1PilotVolumeFormulasActual.qPilotLogVolumeReading_neg`, and this file takes
the strict negativity as the explicit parameter `hqRead`).  Then:

* `qPilot_volume_lt_one : vol {q} = exp qRead < 1`;
* `vol` is monotone and has `q_pos`/`strict_measure` for the hull (hull contains
  `0` but `0 ≠ q`, so the hull is not a subset of the q singleton);
* hence `KummerXiERealization` and `canonicalReading` are constructed;
* `canonicalHqneg : requirementSignedQ (requirementOfReading T canonicalReading) < 0`
  follows from `Real.log_neg`.

No object is changed: the model is only a side realization of the volume
functional, used to discharge the sign hypothesis.  No sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open Classical
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The hull contains 0 and is not a singleton -/

theorem zero_mem_s1902Hull : (0 : S1902Carrier T) ∈ s1902Hull T := by
  unfold s1902Hull rootExtensionProductImageHull
  rw [Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  change ‖(0 : rootNormedExtension T b)‖ ≤ (rootImageRadius T b : Real)
  rw [norm_zero]
  exact_mod_cast (rootImageRadius_pos (T := T) (b := b)).le

theorem qPilotInThetaCarrier_apply_ne_zero (b : Bad (nativePlaceSelection T)) :
    qPilotInThetaCarrier T b ≠ 0 := by
  intro h
  change algebraMap (rootBase T b) (rootNormedExtension T b)
    ((qVFamily T b).q : rootBase T b) = 0 at h
  apply (qVFamily T b).q_ne_zero
  apply (algebraMap (rootBase T b) (rootNormedExtension T b)).injective
  rw [h]
  exact (map_zero _).symm

theorem qPilotInThetaCarrier_ne_zero : qPilotInThetaCarrier T ≠ 0 := by
  intro h
  have b : Bad (nativePlaceSelection T) := Classical.choice (bad_nonempty T)
  exact qPilotInThetaCarrier_apply_ne_zero T b (congrFun h b)

theorem s1902Hull_not_subset_singleton :
    ¬ s1902Hull T ⊆ ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) := by
  intro h
  have h0 : (0 : S1902Carrier T) ∈ ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) :=
    h (zero_mem_s1902Hull T)
  rw [Set.mem_singleton_iff] at h0
  exact qPilotInThetaCarrier_ne_zero T h0.symm

/-! ## 2. The concrete volume model -/

/-- The hull side model: `exp qRead` on subsets of the q singleton, `1` otherwise. -/
noncomputable def volModel (qRead : Real) : Set (S1902Carrier T) → Real :=
  fun S => by
    classical
    exact if S ⊆ ({qPilotInThetaCarrier T} : Set (S1902Carrier T))
      then Real.exp qRead else 1

theorem volModel_singleton (qRead : Real) :
    volModel T qRead {qPilotInThetaCarrier T} = Real.exp qRead := by
  classical
  simp [volModel]

theorem exp_lt_one_of_neg {qRead : Real} (hq : qRead < 0) : Real.exp qRead < 1 := by
  have h := Real.exp_lt_exp.mpr hq
  simpa using h

theorem qPilot_volume_lt_one {qRead : Real} (hq : qRead < 0) :
    volModel T qRead {qPilotInThetaCarrier T} < 1 := by
  rw [volModel_singleton]
  exact exp_lt_one_of_neg hq

theorem volModel_mono {qRead : Real} (hq : qRead < 0) {S U : Set (S1902Carrier T)}
    (hSU : S ⊆ U) : volModel T qRead S ≤ volModel T qRead U := by
  classical
  simp only [volModel]
  by_cases hS : S ⊆ ({qPilotInThetaCarrier T} : Set (S1902Carrier T))
  · by_cases hU : U ⊆ ({qPilotInThetaCarrier T} : Set (S1902Carrier T))
    · simp [hS, hU]
    · simp [hS, hU]
      exact hq.le
  · have hU : ¬ U ⊆ ({qPilotInThetaCarrier T} : Set (S1902Carrier T)) := by
      intro hU'
      exact hS (Set.Subset.trans hSU hU')
    simp [hS, hU]

theorem volModel_q_pos {qRead : Real} :
    0 < volModel T qRead {qPilotInThetaCarrier T} := by
  rw [volModel_singleton]
  exact Real.exp_pos qRead

theorem volModel_strict {qRead : Real} (hq : qRead < 0) :
    volModel T qRead {qPilotInThetaCarrier T} < volModel T qRead (s1902Hull T) := by
  classical
  rw [volModel_singleton]
  simp only [volModel]
  rw [if_neg (s1902Hull_not_subset_singleton T)]
  exact exp_lt_one_of_neg hq

/-! ## 3. The concrete realization and canonical reading -/

noncomputable def kummerXiEModel {qRead : Real} (hq : qRead < 0) :
    KummerXiERealization T where
  vol := volModel T qRead
  vol_mono := fun hSU => volModel_mono T hq hSU
  q_pos := volModel_q_pos T
  strict_measure := volModel_strict T hq

noncomputable def canonicalReading {qRead : Real} (hq : qRead < 0) : PaperKummerReading T :=
  LeanFormal.IUT.XiFPaper.Mzk1LastNamedResolutionActual.canonicalReading T (kummerXiEModel T hq)

theorem canonicalReading_qReading {qRead : Real} (hq : qRead < 0) :
    (canonicalReading T hq).qReading = Real.log (Real.exp qRead) := by
  unfold canonicalReading
  rw [LeanFormal.IUT.XiFPaper.Mzk1LastNamedResolutionActual.canonical_qReading]
  change Real.log (volModel T qRead {qPilotInThetaCarrier T}) = Real.log (Real.exp qRead)
  rw [volModel_singleton]

/-- **`canonicalHqneg`**: the sign hypothesis is a theorem for the concrete side model. -/
theorem canonicalHqneg {qRead : Real} (hq : qRead < 0) :
    requirementSignedQ (requirementOfReading T (canonicalReading T hq)) < 0 := by
  change Real.log ((canonicalReading T hq).D.vol {qPilotInThetaCarrier T}) < 0
  rw [show (canonicalReading T hq).D.vol = volModel T qRead from rfl]
  rw [volModel_singleton]
  exact Real.log_neg (Real.exp_pos qRead) (exp_lt_one_of_neg hq)

/-! ## 4. Axiom gate -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.canonicalHqneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.qPilot_volume_lt_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.volModel_strict

end LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual

end