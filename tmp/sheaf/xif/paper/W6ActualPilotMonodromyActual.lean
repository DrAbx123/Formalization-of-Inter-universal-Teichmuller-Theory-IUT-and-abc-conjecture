import tmp.sheaf.xif.paper.W6LogLocalSystemGroupoidActual
import tmp.sheaf.xif.paper.BadPlaceProcessionNormalizedComparisonActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual

/-!
# W6: the actual procession-normalized qPilot/Theta link as a log local system

This file instantiates the abstract groupoid/monodromy layer of
@W6LogLocalSystemGroupoidActual@ at the **actual** procession-normalized
qPilot and Theta scalars of @BadPlaceProcessionNormalizedComparisonActual@:

* @processionNormalizedQPilotLog@ = sum_b w_b * c_norm_b * log p_b (the
  q-pilot, fixed by the F_l^x procession, S694 label average of a constant);
* @processionNormalizedThetaLog@ = sum_b w_b * (c_norm_b/(2l)) * log p_b
  (the Theta side at the paper root coefficient order/(2l)).

The difference of the two is the monodromy of the link in the
procession-normalized log local system:

  @processionMonodromy@ = qPilotLog - ThetaLog
    = sum_b w_b * c_norm_b * log p_b * (1 - 1/(2l)).

Facts proved here (no gap, no fake input):

* the actual comparison @processionNormalizedComparison@ is exactly the
  nonnegativity of this monodromy;
* Cor 3.12's signed inequality @-qPilotLog <= -ThetaLog@ is *equivalent* to
  nonnegativity of the monodromy along the link (@cor312_iff_monodromy_nonneg@);
* a connector with *zero* monodromy exists iff the two scalars are equal
  (@trivial_monodromy_iff_scalars_eq@), so "trivial monodromy" would be the
  equality of the q-pilot and Theta log volumes, strictly stronger than
  Cor 3.12;
* the monodromy is *strictly positive* whenever the bad-place index is
  nonempty (@processionMonodromy_pos@): the actual link has nontrivial
  monodromy, equal to the paper's @1 - 1/(2l)@ normalization factor.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlaceProcessionNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.W6LogLocalSystemGroupoidActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-! ## 1. The per-place monodromy term -/

/-- The actual per-b contribution to the procession-normalized monodromy: the
q-side coefficient @c_norm * log p@ minus the Theta-side coefficient
@(c_norm/(2l)) * log p@, weighted by the actual local weight. -/
noncomputable def processionTermMonodromy (b : Bad (nativePlaceSelection T)) : Real :=
  nativeBadLocalWeight T b *
    (qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) -
      (qVFamNormalizedCoefficient T b / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real))

/-- The total monodromy of the q -> Theta link in the procession-normalized log
local system. -/
noncomputable def processionMonodromy : Real :=
  ∑ b : Bad (nativePlaceSelection T), processionTermMonodromy T b

/-- The per-place term factors through the paper normalization factor
@1 - 1/(2l)@. -/
theorem processionTermMonodromy_eq (b : Bad (nativePlaceSelection T)) :
    processionTermMonodromy T b =
      nativeBadLocalWeight T b * qVFamNormalizedCoefficient T b *
        Real.log (qVFamTensorP T b : Real) *
          (1 - 1 / (2 * (l.value : Real))) := by
  unfold processionTermMonodromy
  have h2l : (2 * (l.value : Real)) ≠ 0 := by
    have := l.prime.pos
    positivity
  field_simp

/-- The total monodromy is the difference of the actual procession-normalized
qPilot and Theta scalars. -/
theorem processionMonodromy_eq_sub :
    processionMonodromy T =
      processionNormalizedQPilotLog T - processionNormalizedThetaLog T := by
  unfold processionMonodromy processionTermMonodromy
    processionNormalizedQPilotLog processionNormalizedThetaLog
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The actual paper comparison is nonnegativity of the monodromy. -/
theorem processionMonodromy_nonneg : 0 ≤ processionMonodromy T := by
  rw [processionMonodromy_eq_sub]
  exact sub_nonneg.mpr (processionNormalizedComparison T)

/-! ## 2. Strict positivity: the link has nontrivial monodromy -/

theorem one_le_localCompletionDegree (w : NumberField.FinitePlace T.arithmetic.K) :
    1 ≤ localCompletionDegree T.arithmetic w := by
  unfold localCompletionDegree
  exact one_le_finrank_adicCompletion (k := T.arithmetic.Fmod) w

theorem nativeBadLocalWeight_pos (b : Bad (nativePlaceSelection T)) :
    0 < nativeBadLocalWeight T b := by
  unfold nativeBadLocalWeight localNormalizedWeight
  exact inv_pos.mpr (by
    exact_mod_cast one_le_localCompletionDegree (l := l) T (nativeBadToKPlace T b))

/-- Each per-place monodromy term is strictly positive. -/
theorem processionTermMonodromy_pos (b : Bad (nativePlaceSelection T)) :
    0 < processionTermMonodromy T b := by
  rw [processionTermMonodromy_eq]
  have hw : 0 < nativeBadLocalWeight T b := nativeBadLocalWeight_pos T b
  have hc : 0 < qVFamNormalizedCoefficient T b := qVFamNormalizedCoefficient_pos T b
  have hL : 0 < Real.log (qVFamTensorP T b : Real) :=
    Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt)
  have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
  have h2l : (0 : Real) < 2 * (l.value : Real) := by linarith
  have hcoef : 0 < 1 - 1 / (2 * (l.value : Real)) := by
    have hlt : 1 / (2 * (l.value : Real)) < 1 := by
      rw [div_lt_one h2l]
      linarith
    linarith
  exact mul_pos (mul_pos (mul_pos hw hc) hL) hcoef

/-- **Strict positivity.**  If there is at least one bad place, the monodromy of
the actual q -> Theta link is strictly positive: the link is *not*
log-preserving, and the obstruction is exactly the paper's @1 - 1/(2l)@
normalization factor. -/
theorem processionMonodromy_pos [Nonempty (Bad (nativePlaceSelection T))] :
    0 < processionMonodromy T := by
  unfold processionMonodromy
  apply Finset.sum_pos
  · intro b _
    exact processionTermMonodromy_pos T b
  · exact Finset.univ_nonempty

/-- Consequently, in the paper regime the procession-normalized qPilot and Theta
scalars are *different*: the equality case would be a degenerate configuration. -/
theorem processionNormalizedScalars_ne [Nonempty (Bad (nativePlaceSelection T))] :
    processionNormalizedQPilotLog T ≠ processionNormalizedThetaLog T := by
  intro h
  have hpos := processionMonodromy_pos (l := l) T
  rw [processionMonodromy_eq_sub, h, sub_self] at hpos
  exact lt_irrefl 0 hpos

/-! ## 3. The link as an actual morphism of the log-value groupoid -/

/-- The qPilot object: the signed procession-normalized qPilot log. -/
noncomputable def qPilotObjReal : linkGroupoid := -processionNormalizedQPilotLog T

/-- The Theta object: the signed procession-normalized Theta log. -/
noncomputable def thetaObjReal : linkGroupoid := -processionNormalizedThetaLog T

/-- The actual link morphism of the log-value groupoid; its monodromy is the
procession-normalized difference. -/
noncomputable def pilotLink : qPilotObjReal T ⟶ thetaObjReal T :=
  ⟨processionMonodromy T, by
    show -processionNormalizedQPilotLog T + processionMonodromy T =
      -processionNormalizedThetaLog T
    rw [processionMonodromy_eq_sub]
    ring⟩

theorem pilotLink_monodromy :
    linkGroupoid.logSystem.monodromy (pilotLink T) = processionMonodromy T := rfl

/-- **Cor 3.12 as the orientation of the monodromy.**  The signed qPilot/Theta
inequality is *equivalent* to nonnegativity of the monodromy of the actual link
in the log-value groupoid. -/
theorem cor312_iff_monodromy_nonneg :
    qPilotObjReal T ≤ thetaObjReal T ↔ 0 ≤ processionMonodromy T := by
  have h := linkGroupoid.logSystem.le_iff_monodromy_nonneg (pilotLink T)
  rw [pilotLink_monodromy] at h
  exact h

/-- The actual signed comparison (paper direction). -/
theorem cor312_signed_actual : qPilotObjReal T ≤ thetaObjReal T := by
  show -processionNormalizedQPilotLog T ≤ -processionNormalizedThetaLog T
  linarith [processionNormalizedComparison T]

/-- A log-preserving connector exists iff the two scalars are equal. -/
theorem trivial_monodromy_iff_scalars_eq :
    (exists f : qPilotObjReal T ⟶ thetaObjReal T,
      linkGroupoid.logSystem.monodromy f = 0) ↔
      processionNormalizedQPilotLog T = processionNormalizedThetaLog T := by
  rw [linkGroupoid.trivial_monodromy_iff_eq]
  show -processionNormalizedQPilotLog T = -processionNormalizedThetaLog T ↔ _
  constructor <;> intro h <;> linarith

/-- **The no-go.**  In the non-degenerate paper regime no connector has zero
monodromy: the groupoid/path encoding cannot be made log-preserving. -/
theorem no_trivial_monodromy_link [Nonempty (Bad (nativePlaceSelection T))] :
    ∀ f : qPilotObjReal T ⟶ thetaObjReal T,
      linkGroupoid.logSystem.monodromy f ≠ 0 := by
  intro f hf
  have heq : processionNormalizedQPilotLog T = processionNormalizedThetaLog T :=
    (trivial_monodromy_iff_scalars_eq T).mp ⟨f, hf⟩
  exact processionNormalizedScalars_ne T heq

end LeanFormal.IUT.XiFPaper.W6ActualPilotMonodromyActual
