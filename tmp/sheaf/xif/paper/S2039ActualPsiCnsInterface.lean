import tmp.sheaf.xif.paper.S2027LocalArtinActual
/-! # S2039 actual PsiCns interface: M1 actual + exact first missing M2a
This file does not fake PsiCns.  It exposes the actual S2017/S2024/S2027
reduction and records M2a as the exact first missing datum.  The forbidden
IndIntegralMonoid/SourceMLF model is not used. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S2039ActualPsiCnsInterface
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
variable {p : Nat} [Fact p.Prime]
/-- Exact first missing datum of actual PsiCns: levelwise local Artin
ison on torsion plus the abstract/profinite carrier comparison. -/
def S2039FirstMissing : Prop := localArtinSourceDataMissing (p := p)
/-- The exact first missing datum is precisely the S2027 LocalArtinSourceData. -/
theorem S2039FirstMissing_iff :
    S2039FirstMissing (p := p) ↔ Nonempty (LocalArtinSourceData p) := Iff.rfl
/-- M1 + M2b reduction: any actual LocalArtinSourceData and transfer
compatibility give the S2017 muQZ and muHat comparisons. -/
theorem S2039_muQZ_muHat_of_source (d : LocalArtinSourceData p)
    (htransfer : ∀ {H K : Index p} (h : H ≤ K)
      (v : CommGroup.torsion (Abelianization K)),
      levelwiseEquiv p d H (torsionMap (verlagerungOpen p h) v) =
        fixedFieldTorsionUnitsInclusion p h (levelwiseEquiv p d K v)) :
    muQZComparison p ∧ muHatComparison p :=
  ⟨muQZComparison_of_source p d htransfer,
    muHatComparison_of_source p d htransfer⟩
/-- M2a supplies each levelwise local Artin torsion statement. -/
theorem S2039_localArtinTorsion_of_source (d : LocalArtinSourceData p)
    (U : Index p) : localArtinTorsionTopological p U :=
  ⟨d.artin U⟩
end LeanFormal.IUT.XiFPaper.S2039ActualPsiCnsInterface
end
