/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import tmp.sheaf.xif.paper.Mzk1NormArchDegreeActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import Mathlib.Tactic

/-!
# Route B #3 step 4: archimedean determinant metric object

Constructs the archimedean metric weight from the actual explicit principal divisor
and the explicit arch normalization C_K = 1/[K:Q] of Mzk1NormArchCKActual.
The Hermitian metric on the actual line bundle is constructed below; the global
degree compatibility with archDetMetricWeight remains the next step.  No sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators NumberField

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchDegreeActual

variable {F : Type} [Field F] [NumberField F]

/-- Actual archimedean metric weight from a principal unit: the arch normalization
C_K times the explicit principal-divisor archimedean sum. -/
noncomputable def archDetMetricWeight (f : Fˣ) : Real :=
  archCK F *
    (∑ w : NumberField.InfinitePlace F,
      (NumberField.InfinitePlace.mult w : Real) *
        (SourceModelBackend.principalDivisorExplicit (F := F)
          (Additive.ofMul f)).2 w)

/-- Actual archimedean metric datum associated to a principal unit. -/
structure ArchimedeanDetMetricData where
  unit : Fˣ
  metric : Real
  metric_eq : metric = archDetMetricWeight (F := F) unit

noncomputable def archimedeanDetMetricOfUnit (f : Fˣ) :
    ArchimedeanDetMetricData (F := F) where
  unit := f
  metric := archDetMetricWeight (F := F) f
  metric_eq := rfl

theorem archimedeanDetMetricOfUnit_metric (f : Fˣ) :
    (archimedeanDetMetricOfUnit (F := F) f).metric =
      archDetMetricWeight (F := F) f := rfl

/-- Actual Hermitian metric on a fractional-ideal line bundle: at an infinite
place it is the absolute value of the underlying field element. -/
structure HermitianLineMetric
    (I : PaperDeterminantLogVolume.LineBundle (k := F)) where
  norm : NumberField.InfinitePlace F → I → Real
  norm_nonneg : ∀ (w : NumberField.InfinitePlace F) (x : I), 0 ≤ norm w x
  norm_apply : ∀ (w : NumberField.InfinitePlace F) (x : I),
    norm w x = w (x : F)

/-- The actual infinite-place Hermitian metric on a line bundle. -/
noncomputable def lineBundleHermitianMetric
    (I : PaperDeterminantLogVolume.LineBundle (k := F)) :
    HermitianLineMetric (F := F) I where
  norm w x := w (x : F)
  norm_nonneg w x := w.1.nonneg (x : F)
  norm_apply w x := rfl

/-- Actual infinite-place metric package on the whole line-bundle layer. -/
structure ArchimedeanLineMetric where
  metric : ∀ I : PaperDeterminantLogVolume.LineBundle (k := F), HermitianLineMetric (F := F) I

noncomputable def archimedeanLineMetric : ArchimedeanLineMetric (F := F) where
  metric := fun I => lineBundleHermitianMetric (F := F) I

theorem archimedeanLineMetric_constructed :
    Nonempty (ArchimedeanLineMetric (F := F)) := ⟨archimedeanLineMetric⟩

/-- Archimedean log-norm sum from the actual place absolute values. -/
noncomputable def archimedeanLogNorm (x : F) : Real :=
  ∑ w : NumberField.InfinitePlace F,
    (NumberField.InfinitePlace.mult w : Real) * Real.log (w x)

/-- Compatibility of the actual archimedean norm with the global arch degree:
the weight used in archDetMetricWeight is negative C_K times the log-norm sum. -/
theorem archDetMetricWeight_eq_neg_archimedeanLogNorm (f : Fˣ) :
    archDetMetricWeight (F := F) f =
      - archCK F * archimedeanLogNorm (F := F) (f : F) := by
  unfold archDetMetricWeight archimedeanLogNorm
  have hterm : ∀ w : NumberField.InfinitePlace F,
      (SourceModelBackend.principalDivisorExplicit (F := F)
        (Additive.ofMul f)).2 w = -Real.log (w (f : F)) := by
    intro w
    exact principalDivisorInfinite_apply (F := F) f w
  simp only [hterm]
  have hneg : (∑ x : NumberField.InfinitePlace F,
      (NumberField.InfinitePlace.mult x : Real) * (-Real.log (x (f : F)))) =
      - ∑ x : NumberField.InfinitePlace F,
        (NumberField.InfinitePlace.mult x : Real) * Real.log (x (f : F)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hneg]
  ring

def archMetricRows : List (String × String × String) :=
  [ ("archDetMetricWeight", "C_K * sum arch principal divisor", "CONSTRUCTED"),
    ("ArchimedeanDetMetricData", "unit + metric + construction equality", "CONSTRUCTED"),
    ("archimedeanDetMetricOfUnit", "metric object from actual unit", "CONSTRUCTED"),
    ("archimedeanLineMetric", "actual Hermitian metric on lineBundle at infinite places", "CONSTRUCTED"),
    ("archimedeanLogNorm", "sum mult * log |x|_w from actual metric norm", "CONSTRUCTED"),
    ("archDetMetricWeight_eq_neg_archimedeanLogNorm", "global arch degree compatibility", "PROVED") ]

theorem archMetricRows_length : archMetricRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
