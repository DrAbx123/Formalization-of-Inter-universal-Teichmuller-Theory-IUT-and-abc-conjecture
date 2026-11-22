/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1SourceRootIdentityActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotObjectActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import Mathlib.Tactic

/-! # A1073: concrete S1487 source-root identity (canonical logQ) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (canonical identity PROVED; paper-logQ compatibility is a data condition) |
| 结论 | `reduction.qParameter` 是 SourceDefinition31Data 的**数据字段**（S1487SourceData 中为任意 `q : Bad → Real`）；因此 `badQAbsLog = paperQAbsLog l logQ` 只能对待定的 logQ 成立：**取 `logQ := 2l * badQAbsLog` 时恒成立**（`qNormFactor = 1/(2l)`）。paper 的 `logQ = Σ weight·qOrder·logp` 与之相等是**数据条件**，不是普遍定理。 |
| 真证 | `paperQAbsLog_two_l_mul`；`S1487_sourceRootIdentity`（canonical logQ） |
| GAP | GAP-PAPER-LOGQ: `paperQAbsLog l logQ_paper = badQAbsLog`（logQ_paper = LeftHandSide 的 q-divisor）需 S1487 的 qParameter 与 qOrder/weight 的离散识别，未证 |
| 循环性 | no target assumed; canonical logQ is an explicit definition, not a target assumption |

This file contains no sorry and no axiom. -/

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.Mzk1SourceRootIdentityActual
open LeanFormal.IUT.XiFPaper.OrigXiF.OrigXiFPaperQPilotObjectActual

namespace LeanFormal.IUT.XiFPaper.Mzk1S1487SourceRootIdentityActual

variable {l : PrimeGeFive}

/-- `paperQAbsLog l (2l * x) = x` (from `qNormFactor l = 1/(2l)`). -/
theorem paperQAbsLog_two_l_mul (l : PrimeGeFive) (x : Real) :
    paperQAbsLog l (2 * (l.value : Real) * x) = x := by
  rw [paperQAbsLog_eq_logQ_div]
  have hl0 : (2 * (l.value : Real)) ≠ 0 := by
    have hpos : 0 < (l.value : Real) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) l.ge_five)
    positivity
  have hl : (l.value : Real) ≠ 0 := by
    intro h
    apply hl0
    rw [h]
    ring
  field_simp [hl]

/-- The canonical logQ for an S1487 faithful source: `2l * badQAbsLog`. -/
noncomputable def S1487CanonicalLogQ (l : PrimeGeFive) : Real :=
  2 * (l.value : Real) * OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l))

/-- The S1487 input used for the source-root identity. -/
noncomputable def S1487RootInput (l : PrimeGeFive) :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487OriginalInput (l := l) (S1487FaithfulSourceData (l := l))

/-- The S1487 input's initial source datum is the faithful source datum. -/
theorem S1487RootInput_initial (l : PrimeGeFive) :
    (S1487RootInput l).initial = S1487FaithfulSourceData (l := l) := rfl

/-- **Concrete S1487 source-root identity** with the canonical logQ:
`badQAbsLog = paperQAbsLog l (2l * badQAbsLog)`. -/
theorem S1487_sourceRootIdentity (l : PrimeGeFive) :
    SourceRootIdentity (l := l) (I := S1487RootInput l) (S1487CanonicalLogQ l) := by
  unfold SourceRootIdentity S1487CanonicalLogQ
  rw [S1487RootInput_initial]
  rw [paperQAbsLog_two_l_mul]

/-- The paper-logQ compatibility is a DATA condition, recorded explicitly. -/
def PaperLogQCompatibility (l : PrimeGeFive)
    (logQ : Real) : Prop :=
  OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l)) = paperQAbsLog l logQ

/-- A sufficient concrete form: `paperQAbsLog` compatibility with the canonical logQ. -/
theorem S1487_paperLogQCompatibility_canonical (l : PrimeGeFive) :
    PaperLogQCompatibility l (S1487CanonicalLogQ l) := by
  unfold PaperLogQCompatibility
  rw [show S1487CanonicalLogQ l = 2 * (l.value : Real) * OrigXiFPaperBadQAbsLog (S1487FaithfulSourceData (l := l)) from rfl]
  exact (paperQAbsLog_two_l_mul l _).symm

def s1487RootRows : List (String × String) :=
  [ ("paperQAbsLog_two_l_mul", "paperQAbsLog l (2l*x) = x (PROVED)") ,
    ("S1487CanonicalLogQ", "logQ := 2l * badQAbsLog") ,
    ("S1487_sourceRootIdentity", "concrete identity with canonical logQ (PROVED)") ,
    ("GAP-PAPER-LOGQ", "logQ from qOrder/weight equals 2l*badQAbsLog is a data condition") ]

theorem s1487RootRows_length : s1487RootRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S1487SourceRootIdentityActual