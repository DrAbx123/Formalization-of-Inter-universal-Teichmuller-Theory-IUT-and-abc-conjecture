import tmp.sheaf.xif.paper.Mzk1ContinuousAddZpadicActual
import LeanFormal.IUT.Foundations.LocalFields.ContinuousRationalPadicScalars
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmRationalization
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1WFLatticeActionActual
open LeanFormal.IUT.XiFPaper.Mzk1ContinuousAddZpadicActual
open LeanFormal.IUT.LocalFieldPadicScalars
open LeanFormal.IUT.LocalFieldLogarithm

universe uW uW'
variable {p : Nat} [Fact p.Prime]

/-- Exact remaining source input for the general Ind1 `β_a`: the actual
identification of the source unit quotient with the integral units, plus the
derivation of `β_a` from the source action.  No inhabitant is supplied. -/
structure WFUnitQuotientIdentification (p : Nat) [Fact p.Prime] (W : Type uW) [AddCommGroup W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] (d : Nat) where
  sourceUnitQuotient : Type
  [addCommGroup : AddCommGroup sourceUnitQuotient]
  sourceAddEquiv : sourceUnitQuotient ≃+ W
  wEquiv : W ≃ₜ+ (Fin d → ℤ_[p])
  identificationSource : Prop
  betaFromSourceAction : Prop

def WFUnitQuotientIdentificationRequired (p : Nat) [Fact p.Prime] (W : Type uW) [AddCommGroup W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] (d : Nat) : Prop :=
  Nonempty (WFUnitQuotientIdentification p W d)
theorem wfIdentificationRequired_iff (W : Type uW) [AddCommGroup W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] (d : Nat) :
    WFUnitQuotientIdentificationRequired p W d ↔
      Nonempty (WFUnitQuotientIdentification p W d) := Iff.rfl

#print axioms wfIdentificationRequired_iff
end LeanFormal.IUT.XiFPaper.Mzk1WFLatticeActionActual