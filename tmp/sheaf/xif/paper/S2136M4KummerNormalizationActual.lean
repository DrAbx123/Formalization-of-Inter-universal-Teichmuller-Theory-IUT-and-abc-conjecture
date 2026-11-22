import tmp.sheaf.xif.paper.S2091H2ZhatActual
import tmp.sheaf.xif.paper.S2112ContH2LimitActual
import tmp.sheaf.xif.paper.S2036ActualPsiCnsM234Actual

-- S2136 M4: exact normalization/Kummer-image surface.  The ported H2/Br
-- data and the Z^2 exchange are actual; the cup-product normalization
-- map and its Kummer-image property remain exact first missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2136M4KummerNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2036ActualPsiCnsM234Actual
open LeanFormal.IUT.XiFPaper.S2091H2ZhatActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Ported H^2(ℚ_p, Ẑ(1)) ≃ Ẑ. -/
noncomputable abbrev S2136H2ZHatEquiv :
    Brauer.H2ZHatOne ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Zhat :=
  h2ZHatOneEquiv_of_port p

/-- Ported Br(ℚ_p) ≃ ℚ/ℤ. -/
noncomputable abbrev S2136BrEquivQZ :
    Brauer.Br ℚ_[p] (AlgebraicClosure ℚ_[p]) ≃*
      Multiplicative Brauer.QZ :=
  brEquivQZ p

/-- The exact M4 normalization data: a surjective normalization of the
actual continuous H^1 limit, whose inverse image of the nonnegative
Ẑ is exactly the Kummer image and whose kernel on that image is the
unit subgroup. -/
structure S2136M4NormalizationData where
  norm : PsiCnsCohomology p →* Multiplicative Zhat
  surjective : Function.Surjective norm
  kummer_image :
    MonoidHom.mrange (PsiCnsKummer p) =
      Submonoid.comap norm zhatNatMonoid
  kernel_units :
    ∀ a : Otri p, norm (PsiCnsKummer p a) = 1 ↔
      ∃ u : (Otri p)ˣ, (u : Otri p) = a

/-- Exact M4 proposition, unchanged. -/
abbrev S2136M4KummerNormalizationRequired : Prop :=
  PsiCnsKummerNormalization p

/-- Conditional actual M4 from the exact normalization data. -/
theorem S2136M4_of_data (D : S2136M4NormalizationData p) :
    PsiCnsKummerNormalization p :=
  ⟨D.norm, D.surjective, D.kummer_image, D.kernel_units⟩

/-- The data surface is exactly the first missing cup-product normalization. -/
abbrev S2136M4CupProductNormalizationRequired : Type :=
  S2136M4NormalizationData p

#check S2136H2ZHatEquiv
#check S2136BrEquivQZ
#check S2136M4NormalizationData
#check S2136M4KummerNormalizationRequired
#check S2136M4_of_data
#check S2136M4CupProductNormalizationRequired

#print axioms S2136H2ZHatEquiv
#print axioms S2136BrEquivQZ
#print axioms S2136M4_of_data

end LeanFormal.IUT.XiFPaper.S2136M4KummerNormalizationActual

end