import tmp.sheaf.xif.paper.S2136M4KummerNormalizationActual
import tmp.sheaf.xif.paper.S2112ContH2LimitActual

-- S2140: M4 cup-product normalization attempt.  The H2/Br port and the
-- Z^2 exchange are actual; the cup-product normalization map itself is
-- the exact first missing.  No M3/M4 assumption, no fake.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2140M4CupProductActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2091H2ZhatActual
open LeanFormal.IUT.XiFPaper.S2136M4KummerNormalizationActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Actual H2(Ẑ) port. -/
noncomputable abbrev S2140H2ZHatEquiv :
    Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Zhat :=
  S2136H2ZHatEquiv p

/-- Actual Br(Q_p) ≃ Q/Z port. -/
noncomputable abbrev S2140BrEquivQZ :
    Brauer.Br ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Brauer.QZ :=
  S2136BrEquivQZ p

/-- Exact first missing map: the cup-product normalization on the actual
continuous H^1 limit. -/
abbrev S2140CupProductMapRequired : Type :=
  PsiCnsCohomology p →* Multiplicative Zhat

/-- Exact first missing surjective normalization map. -/
abbrev S2140SurjectiveNormalizationRequired : Type :=
  { norm : PsiCnsCohomology p →* Multiplicative Zhat //
      Function.Surjective norm }

/-- The full M4 normalization data, re-exported from S2136. -/
abbrev S2140CupProductNormalizationRequired : Type :=
  S2136M4NormalizationData p

/-- Conditional actual M4 from the data. -/
theorem S2140M4_of_data (D : S2140CupProductNormalizationRequired p) :
    PsiCnsKummerNormalization p :=
  S2136M4_of_data p D

#check S2140H2ZHatEquiv
#check S2140BrEquivQZ
#check S2140CupProductMapRequired
#check S2140SurjectiveNormalizationRequired
#check S2140CupProductNormalizationRequired
#check S2140M4_of_data

#print axioms S2140H2ZHatEquiv
#print axioms S2140BrEquivQZ
#print axioms S2140M4_of_data

end LeanFormal.IUT.XiFPaper.S2140M4CupProductActual

end