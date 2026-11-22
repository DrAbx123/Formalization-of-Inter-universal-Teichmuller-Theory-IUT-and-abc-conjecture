/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import Mathlib.Tactic

/-!
# P6-B6: QCAND final assembly of the two explicit subgaps

Status: CONDITIONAL.  Single declaration cluster re-exporting the QCAND
decomposition from `Mzk1C17QCANDOrderResidueActual`.  No new assumption.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Final QCAND assembly: ORDER + RESNORM imply pointwise QCAND. -/
theorem qcand_assembly
    (hord : QCANDOrderGap T) (hres : QCANDResNormGap T) :
    ∀ b, QCANDAt T b :=
  qcand_of_order_resnorm T hord hres

def qcandAssemblyRows : List (String × String × String) :=
  [ ("qcand_assembly", "QCANDOrderGap + QCANDResNormGap => QCAND", "PROVED (re-export)") ]

theorem qcandAssemblyRows_length : qcandAssemblyRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDAssemblyActual
