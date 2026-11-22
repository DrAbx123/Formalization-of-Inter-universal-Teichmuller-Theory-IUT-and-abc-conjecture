/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ind1WQuotientFiveIsoActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import Mathlib.Tactic

/-! # Route N3 §7.4: WQuotient actual inhabitant data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1TaskEWQuotientFiveInhabitantActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1Ind1WQuotientFiveIsoActual

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Exact data still needed for the actual §7.4 inhabitant: the
uniformizer/irreducible certificate for `5` in `Integers ℚ_[5]`, the
integer-ring identification `Integers ℚ_[5] ≃+* ℤ_[5]`, and the resulting
unit-quotient isomorphism.  No inhabitant is supplied. -/
structure WQuotientFiveInhabitantData where
  hpi : Irreducible (5 : Integers ℚ_[5])
  integersEquiv : Integers ℚ_[5] ≃+* ℤ_[5]
  iso :
    ((Integers ℚ_[5])ˣ ⧸ CommGroup.torsion ((Integers ℚ_[5])ˣ)) ≃*
      Multiplicative ℤ_[5]

def WQuotientFiveInhabitantRequired : Prop :=
  Nonempty WQuotientFiveInhabitantData

def WQuotientFiveInhabitantData.toIso
    (D : WQuotientFiveInhabitantData) : WQuotientFiveIso where
  equiv := D.iso

end LeanFormal.IUT.XiFPaper.Mzk1TaskEWQuotientFiveInhabitantActual
