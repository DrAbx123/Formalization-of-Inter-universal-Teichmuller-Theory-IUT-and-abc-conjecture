import tmp.sheaf.xif.paper.S2036ActualPsiCnsM234Actual
import tmp.sheaf.xif.paper.S2090EvaluatedUnitsBridgeActual
import tmp.sheaf.xif.paper.S2039ActualPsiCns

-- S2046 M4 conditional port: from PsiCnsKummerNormalization get the
-- actual unit equivalence local O^x -> normalization inverse image;
-- M2/M3/M4 remain exact missing hypotheses.  No fake.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046M4ConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2090EvaluatedUnitsBridgeActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- M2 exact first missing (S2036). -/
abbrev S2046M2LocalArtinRequired : Prop := M2FirstMissing p

/-- M3 exact first missing: H^2 = Zhat (S2036). -/
abbrev S2046M3H2Required : Prop := PsiCnsH2Normalization p

/-- M4 exact first missing: normalized surjection + Kummer image (S2036). -/
abbrev S2046M4KummerNormalizationRequired : Prop := PsiCnsKummerNormalization p

/-- The actual normalization from M4. -/
noncomputable def S2046M4NormalizationOfKummer
    (h : PsiCnsKummerNormalization p) :
    { nu : PsiCnsCohomology p →* Multiplicative Zhat // Function.Surjective nu } :=
  ⟨(kummerImage_equiv_nonnegative_of_normalization p h).choose,
    (kummerImage_equiv_nonnegative_of_normalization p h).choose_spec.1⟩

/-- Conditional actual M4 units equivalence: the units of Otri p are the
units of the normalization inverse image. -/
noncomputable def S2046M4OtriUnitsEquivNormalization
    (h : PsiCnsKummerNormalization p) :
    (Otri p)ˣ ≃* (Submonoid.comap
      (kummerImage_equiv_nonnegative_of_normalization p h).choose zhatNatMonoid)ˣ :=
  Units.mapEquiv (Classical.choice
    (kummerImage_equiv_nonnegative_of_normalization p h).choose_spec.2)

/-- Conditional actual local O^x -> M4 normalization comparison, obtained by
composing the S2090 unconditional local-units bridge with the M4 units
equivalence. -/
noncomputable def S2046M4LocalUnitsEquivNormalization
    (h : PsiCnsKummerNormalization p) :
    LocalOFieldUnits p ≃* (Submonoid.comap
      (kummerImage_equiv_nonnegative_of_normalization p h).choose zhatNatMonoid)ˣ :=
  (S2046LocalUnitsEquivOtriUnits p).symm.trans
    (S2046M4OtriUnitsEquivNormalization p h)

/-- M4 reduction: the S2036 M4 proposition yields the actual normalization
inverse-image units equivalence. -/
theorem S2046M4_sufficient (h : PsiCnsKummerNormalization p) :
    Nonempty (LocalOFieldUnits p ≃*
      (Submonoid.comap
        (kummerImage_equiv_nonnegative_of_normalization p h).choose zhatNatMonoid)ˣ) :=
  ⟨S2046M4LocalUnitsEquivNormalization p h⟩

/-- Exact missing comparison between the S2036 zhatNatMonoid and the S2039
zhatNonneg used in PsiCns; if proved, the M4 target is definitionally
PsiCns p N. -/
def S2046ZhatNonnegEqNatMonoid : Prop :=
  (∀ x : Multiplicative Zhat, x ∈ zhatNatMonoid ↔
    x ∈ LeanFormal.IUT.XiFPaper.S2039ActualPsiCns.zhatNonneg)

#check S2046M2LocalArtinRequired
#check S2046M3H2Required
#check S2046M4KummerNormalizationRequired
#check S2046M4NormalizationOfKummer
#check S2046M4OtriUnitsEquivNormalization
#check S2046M4LocalUnitsEquivNormalization
#check S2046M4_sufficient
#check S2046ZhatNonnegEqNatMonoid

#print axioms S2046M4OtriUnitsEquivNormalization
#print axioms S2046M4LocalUnitsEquivNormalization
#print axioms S2046M4_sufficient

end LeanFormal.IUT.XiFPaper.S2046M4ConditionalActual

end