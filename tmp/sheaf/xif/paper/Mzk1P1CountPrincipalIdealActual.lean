/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1PrincipalValuationProofActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: count of a principal ideal -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountPrincipalIdealActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

def CountPrincipalIdealStatement : Prop :=
  forall (a : NumberField.RingOfIntegers k) (_ : a ≠ 0)
    (v : NumberField.FinitePlace k),
    countExponent (k := k) v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers k))
        (algebraMap (NumberField.RingOfIntegers k) k a)) =
      ((Associates.mk (LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime v).asIdeal).count
        (Associates.mk (Ideal.span {a})).factors : Int)

def countPrincipalRows : List (String × String × String) :=
  [ ("CountPrincipalIdealStatement", "count_v(spanSingleton a) = Associates count", "GAP (principal count identification)"),
    ("valuation side", "localValuation (algebraMap a) = -count", "PROVED") ]

theorem countPrincipalRows_length : countPrincipalRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1CountPrincipalIdealActual

end
