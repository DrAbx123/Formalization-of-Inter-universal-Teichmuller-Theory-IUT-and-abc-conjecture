/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic

/-! # R29s / task-99: actual bad-place → F-place map and per-place valuation equality -/

/-
| field | value |
|---|---|
| Status | PARTIAL/green: actual place map `qVFamTensorPlace : Bad -> FinitePlace F` identified; per-place `|log ‖q_b‖| = order_b * log(residueNormBase place_b)` proved; sum form proved; source-q identification is an explicit GAP |
| Reuse | `QVFamTensorCoefficientActual:47 qVFamTensorPlace`（actual map via nativeBadLift), `:51 qVFamTensorP`, `:76 qVFamTensorCoefficient`; `QPilotZeroLocusDivisorActual:55 qVFamily`; `QVFamNormalizedCoefficientBridgeActual:59 qVFamDefaultNorm`, `:92 localLogMagnitude_qVFamily_eq`; `ArithmeticQPilotBaseChange:71 localLogMagnitude_eq_order_mul_log`；`ArithmeticQPilotLogVolume:46 localLogMagnitude_pos` |
| GAP | GAP-SOURCE-NATIVE-Q: contract `qParameter` family vs native `qVFamDefaultNorm` family (index type + values) not identified; explicit `hf` hypothesis is the interface |
| GAP | GAP-DEGREE-EXPLICIT: constructing `SourceModelBackend.ExplicitDivisor F` from the bad-place map (Finsupp/height-one-spectrum, arch zero) and proving its degree equals the native valuation sum is not done |
| GAP | GAP-DEGREE-RES: `residueNormBase place = qVFamTensorP` (degree one / obstruction) is a separate condition; given as hypothesis `hres` |
| 纪律 | no sorry/axiom; per-place and sum identities are real theorems; identification hypotheses are explicit |
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotPlaceDegreeActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The actual bad-place → F-place map -/

/-- The actual F-place map on the native bad index: the Definition 3.1(e) lift of b.
This is the place map needed for the q-side degree bridge (no Prop placeholder). -/
noncomputable abbrev nativeBadToFinitePlace :
    Bad (nativePlaceSelection T) → NumberField.FinitePlace T.arithmetic.F :=
  qVFamTensorPlace T

theorem nativeBadToFinitePlace_apply (b : Bad (nativePlaceSelection T)) :
    nativeBadToFinitePlace T b = (nativeBadLift T).lift b := rfl

theorem nativeBadToFinitePlace_rationalPrime (b : Bad (nativePlaceSelection T)) :
    (completionRationalPrime (nativeBadToFinitePlace T b)).val = qVFamTensorP T b := rfl

/-! ## 2. Per-place valuation equality -/

/-- **Per-place equality (native q)**: `|log ‖q_b‖| = order_b * log(residueNormBase place_b)`.
Here `q_b` is the actual clause-B comparison parameter `qVFamily T b`; the log uses the
place `qVFamTensorPlace T b`. -/
theorem nativeBadPlace_abs_log_eq :
    |Real.log (qVFamDefaultNorm T b)| =
      qVFamTensorCoefficient T b *
        Real.log (residueNormBase (qVFamTensorPlace T b)) := by
  have hlog : localLogMagnitude (qVFamily T b) =
      qVFamTensorCoefficient T b *
        Real.log (residueNormBase (qVFamTensorPlace T b)) := by
    have h := localLogMagnitude_eq_order_mul_log (qVFamily T b)
    simpa [qVFamTensorCoefficient] using h
  have hneg : Real.log (qVFamDefaultNorm T b) = -localLogMagnitude (qVFamily T b) := by
    linarith [localLogMagnitude_qVFamily_eq T b]
  have hpos : 0 < qVFamTensorCoefficient T b *
      Real.log (residueNormBase (qVFamTensorPlace T b)) := by
    rw [← hlog]
    exact localLogMagnitude_pos (qVFamily T b)
  have hpos' : 0 < localLogMagnitude (qVFamily T b) := by
    rw [hlog]
    exact hpos
  calc |Real.log (qVFamDefaultNorm T b)| = |-localLogMagnitude (qVFamily T b)| := by rw [hneg]
    _ = localLogMagnitude (qVFamily T b) := by rw [abs_neg, abs_of_pos hpos']
    _ = qVFamTensorCoefficient T b *
        Real.log (residueNormBase (qVFamTensorPlace T b)) := hlog

/-- **Per-place equality in rational-prime form**, under the residue-degree condition
`residueNormBase = qVFamTensorP` (given explicitly; not assumed for all places). -/
theorem nativeBadPlace_abs_log_eq_logP
    (hres : residueNormBase (qVFamTensorPlace T b) = qVFamTensorP T b) :
    |Real.log (qVFamDefaultNorm T b)| =
      qVFamTensorCoefficient T b * Real.log (qVFamTensorP T b : Real) := by
  rw [nativeBadPlace_abs_log_eq (T := T) (b := b)]
  congr 1
  rw [hres]

/-! ## 3. Sum form over the bad index -/

/-- Sum over theactual finite bad index of the per-place absolute logs. -/
noncomputable def nativeBadQAbsLogSum : Real :=
  ∑ b : Bad (nativePlaceSelection T), |Real.log (qVFamDefaultNorm T b)|

/-- The valuation sum in the order × residue-log normalization. -/
noncomputable def nativeBadValuationSum : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    qVFamTensorCoefficient T b * Real.log (residueNormBase (qVFamTensorPlace T b))

theorem nativeBadQAbsLogSum_eq_valuationSum :
    nativeBadQAbsLogSum T = nativeBadValuationSum T :=
  Finset.sum_congr rfl (fun b _ => nativeBadPlace_abs_log_eq (T := T) (b := b))

theorem nativeBadQAbsLogSum_eq_valuationSum_logP
    (hres : ∀ b, residueNormBase (qVFamTensorPlace T b) = qVFamTensorP T b) :
    nativeBadQAbsLogSum T =
      ∑ b : Bad (nativePlaceSelection T),
        qVFamTensorCoefficient T b * Real.log (qVFamTensorP T b : Real) := by
  rw [nativeBadQAbsLogSum_eq_valuationSum]
  exact Finset.sum_congr rfl (fun b _ => by
    rw [hres b])

/-! ## 4. Source-q identification interface (explicit GAP) -/

/-- Source-level bad-q absolute-log sum for a family indexed by the native bad places. -/
noncomputable def sourceBadQAbsLogFamily
    (f : Bad (nativePlaceSelection T) → Real) : Real :=
  ∑ b : Bad (nativePlaceSelection T), |Real.log (f b)|

/-- **Conditional bridge**: if each contract q-parameter has the same absolute log as the
native qVFamily norm, the source bad-q absolute-log sum equals the native valuation sum.
This is the exact interface for GAP-SOURCE-NATIVE-Q. -/
theorem sourceBadQAbsLogFamily_eq_valuationSum
    (f : Bad (nativePlaceSelection T) → Real)
    (hf : ∀ b, |Real.log (f b)| = |Real.log (qVFamDefaultNorm T b)|) :
    sourceBadQAbsLogFamily T f = nativeBadValuationSum T := by
  rw [sourceBadQAbsLogFamily]
  calc
    (∑ b : Bad (nativePlaceSelection T), |Real.log (f b)|)
        = ∑ b, |Real.log (qVFamDefaultNorm T b)| := by
          exact Finset.sum_congr rfl (fun b _ => hf b)
      _ = nativeBadValuationSum T := nativeBadQAbsLogSum_eq_valuationSum T

def placeDegreeRows : List (String × String) :=
  [ ("nativeBadToFinitePlace", "actual map Bad -> FinitePlace F (via nativeBadLift)") ,
    ("nativeBadPlace_abs_log_eq", "|log||q_b||| = order_b * log residueNormBase (PROVED)") ,
    ("nativeBadPlace_abs_log_eq_logP", "same with residueNormBase = p (hres hypothesis)") ,
    ("nativeBadQAbsLogSum_eq_valuationSum", "sum form (PROVED)") ,
    ("nativeBadQAbsLogSum_eq_valuationSum_logP", "sum in rational-prime form (hres) (PROVED)") ,
    ("sourceBadQAbsLogFamily_eq_valuationSum", "source-q bridge (hf hypothesis; PROVED conditionally)") ,
    ("GAP-SOURCE-NATIVE-Q", "contract qParameter family vs native qVFamDefaultNorm (index+values) missing") ,
    ("GAP-DEGREE-EXPLICIT", "ExplicitDivisor construction from bad-place map missing") ,
    ("GAP-DEGREE-RES", "residueNormBase = qVFamTensorP (degree one/obstruction) is a condition") ]

theorem placeDegreeRows_length : placeDegreeRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QPilotPlaceDegreeActual