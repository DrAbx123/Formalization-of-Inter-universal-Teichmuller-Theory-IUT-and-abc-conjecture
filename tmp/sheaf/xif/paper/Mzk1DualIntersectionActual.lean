/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1MultiFactorBlockActual
import tmp.sheaf.xif.paper.Mzk1MinimalAcceptanceActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualLattice

/-!
# qVFam actual trace Gram and dual intersection (task-102, partial)

Status: PARTIAL actual-node.  This file defines the actual trace form and
trace Gram matrix on the qVFamTensorBlock using the chosen Z_p-integral
basis from IntegralTraceDualTensorInclusion, and defines the actual trace
dual `XG` of the task-90 `LambdaG`.

The matrix condition `XG = {x | G^T S x in Z_p^r}` and the general-lattice
same-relative-volume theorem are NOT proved here; they are recorded as exact
GAPs in coord/P3-MINIMAL-ACCEPTANCE.md.  No sorry/axiom/PUnit/True.
-/

noncomputable section
open scoped BigOperators LeanFormal.IUT.FinitePadicIntegralLattice
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DualIntersectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.IntegralTraceDual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1MultiFactorBlockActual
open LeanFormal.IUT.XiFPaper.Mzk1MinimalAcceptanceActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The actual trace form on the qVFam tensor block. -/
noncomputable def qVFamTraceForm :
    LinearMap.BilinForm ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b) :=
  Algebra.traceForm ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)

/-- Index type of the chosen Z_p-integral basis of the tensor block. -/
abbrev QVFamBasisIndex : Type _ :=
  (i : qVFamTensorV) → arithmeticTupleLocalBasisIndex
    (qVFamTensorPlaces T b) qVFamTensorTuple i

/-- The actual chosen Q_p-basis extending the Z_p-integral basis. -/
noncomputable def qVFamTraceBasis :
    Module.Basis (QVFamBasisIndex (l := l) T b) ℚ_[(qVFamTensorP T b)]
      (qVFamTensorBlock T b) :=
  arithmeticTupleValuationIntegerQpBasis
    (qVFamTensorPlaces T b) qVFamTensorTuple

/-- The actual trace Gram matrix `S` in the chosen integral basis. -/
noncomputable def qVFamTraceGram :
    Matrix (QVFamBasisIndex (l := l) T b) (QVFamBasisIndex (l := l) T b)
      ℚ_[(qVFamTensorP T b)] :=
  Matrix.of fun i j =>
    qVFamTraceForm (l := l) T b (qVFamTraceBasis (l := l) T b i)
      (qVFamTraceBasis (l := l) T b j)

theorem qVFamTraceGram_apply
    (i j : QVFamBasisIndex (l := l) T b) :
    qVFamTraceGram (l := l) T b i j =
      Algebra.traceForm ℚ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)
        (qVFamTraceBasis (l := l) T b i) (qVFamTraceBasis (l := l) T b j) :=
  rfl

/-- The actual trace dual of the task-90 `LambdaG`.  This is the dual-side
object; its matrix description `{x | G^T S x in Z_p^r}` is the next GAP. -/
noncomputable def XG : Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b) :=
  padicIntegralTraceDualLattice (qVFamTraceForm (l := l) T b)
    (LambdaG (l := l) T b)

theorem XG_eq_traceDual :
    XG (l := l) T b =
      padicIntegralTraceDualLattice (qVFamTraceForm (l := l) T b)
        (LambdaG (l := l) T b) :=
  rfl

def dualRows : List (String × String) :=
  [ ("qVFamTraceForm", "actual trace form"),
    ("qVFamTraceGram", "actual S from integral basis"),
    ("XG", "actual trace dual of LambdaG"),
    ("XG = matrix intersection", "GAP"),
    ("same relative volume", "GAP (general B4/B5)") ]

theorem dualRows_length : dualRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DualIntersectionActual
