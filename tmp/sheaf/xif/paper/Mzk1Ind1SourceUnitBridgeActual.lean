import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import tmp.sheaf.xif.paper.Mzk1Ind1AlgebraicUnitQuotientActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1SourceUnitBridgeActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe uK uL uW uW'
variable {K : Type uK} [NormedField K] [IsUltrametricDist K]
variable {L : Type uL} [NormedField L] [IsUltrametricDist L]
variable {p : Nat} [Fact p.Prime]
variable [CharZero K] [CompleteSpace K] [ProperSpace K]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]

/-- The actual source unit quotient identified with the integral units modulo
torsion.  This is the missing source-level identification; no inhabitant is
supplied. -/
structure SourceUnitQuotientIdentification (W : Type uW) [CommGroup W]
    (K : Type uK) [NormedField K] [IsUltrametricDist K] where
  equiv : W ≃* ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ)

/-- Given actual source-unit identifications and an actual source unit action,
build the induced isomorphism of actual log-images. -/
def sourceUnitLogRangeEquiv
    {W : Type uW} [CommGroup W] {W' : Type uW'} [CommGroup W']
    (idK : SourceUnitQuotientIdentification W K)
    (idL : SourceUnitQuotientIdentification W' L)
    (β : W ≃* W') :
    (unitLogHom (K := K) (p := p)).range ≃*
      (unitLogHom (K := L) (p := p)).range :=
  (unitLogTorsionQuotientEquivRange (K := K) (p := p)).symm.trans
    (idK.equiv.symm.trans (β.trans
      (idL.equiv.trans (unitLogTorsionQuotientEquivRange (K := L) (p := p)))))

theorem sourceUnitLogRangeEquiv_apply
    {W : Type uW} [CommGroup W] {W' : Type uW'} [CommGroup W']
    (idK : SourceUnitQuotientIdentification W K)
    (idL : SourceUnitQuotientIdentification W' L)
    (β : W ≃* W')
    (q : (unitLogHom (K := K) (p := p)).range) :
    sourceUnitLogRangeEquiv (p := p) idK idL β q =
      (unitLogTorsionQuotientEquivRange (K := L) (p := p))
        (idL.equiv (β (idK.equiv.symm
          ((unitLogTorsionQuotientEquivRange (K := K) (p := p)).symm q)))) := rfl

#print axioms sourceUnitLogRangeEquiv_apply

/-- Tautological self-identification: `W` chosen as the target integral-unit
torsion quotient.  This is an actual inhabitant of the structure, but it is
NOT the source-level W identification; it only records that the interface is
consistent. -/
def sourceUnitQuotientIdentification_self (K : Type uK) [NormedField K]
    [IsUltrametricDist K] :
    SourceUnitQuotientIdentification
      ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) K where
  equiv := MulEquiv.refl _

theorem sourceUnitQuotientIdentification_self_nonempty (K : Type uK)
    [NormedField K] [IsUltrametricDist K] :
    Nonempty (SourceUnitQuotientIdentification
      ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) K) :=
  ⟨sourceUnitQuotientIdentification_self K⟩

#print axioms sourceUnitQuotientIdentification_self_nonempty

/-- Identity consistency of the actual log-range bridge: self-identification
and identity source action give an endomorphism of the actual log range. -/
def sourceUnitLogRangeEquiv_self (K : Type uK) [NormedField K]
    [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] :
    (unitLogHom (K := K) (p := p)).range ≃*
      (unitLogHom (K := K) (p := p)).range :=
  sourceUnitLogRangeEquiv (p := p)
    (sourceUnitQuotientIdentification_self K)
    (sourceUnitQuotientIdentification_self K) (MulEquiv.refl _)

end LeanFormal.IUT.XiFPaper.Mzk1Ind1SourceUnitBridgeActual