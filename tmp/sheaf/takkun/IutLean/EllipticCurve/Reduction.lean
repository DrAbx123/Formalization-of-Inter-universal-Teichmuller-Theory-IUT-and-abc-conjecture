import Mathlib

/-!
# 楕円曲線の安定(半安定)還元 (Track B / [IUT-I] Def 3.1(b))

底本: [IUT-I] Definition 3.1 (b)(「`X_F` は全非アルキメデス素点で安定還元を持つ」)。

楕円曲線に対し、**安定還元** (stable reduction) とは**半安定還元** (semistable reduction) の
ことであり、各局所体上で**良還元または乗法的還元**を持つこと(同値: 加法的還元を持たないこと)。

Mathlib の `WeierstrassCurve.HasGoodReduction` / `HasMultiplicativeReduction` /
`HasAdditiveReduction`(離散付値環 `R` 上の極小 Weierstrass 方程式)と還元の三分律を用いて、
この特徴付け **半安定 ⟺ ¬加法的** を `sorry` 無しに証明する。これは
`HasStableReductionEverywhere`(全素点での安定還元)を将来具体化するための Track B 基盤。
-/

namespace IUT.EllipticCurve

open WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve K} [IsMinimal R W]

/-- 楕円曲線の**安定(半安定)還元**: 良還元または乗法的還元を持つこと
([IUT-I] Def 3.1(b) の「stable reduction」)。 -/
def IsSemistable : Prop := W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R

/-- **安定還元 ⟺ 加法的還元を持たない**(還元の三分律と相互排他性より)。
Def 3.1(b) の安定還元条件の特徴付け。 -/
theorem isSemistable_iff_not_hasAdditiveReduction :
    IsSemistable R (W := W) ↔ ¬ W.HasAdditiveReduction R := by
  constructor
  · rintro (h | h)
    · exact h.not_hasAdditiveReduction
    · exact h.not_hasAdditiveReduction
  · intro h
    rcases hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
      (R := R) (W := W) with hg | hm | ha
    · exact Or.inl hg
    · exact Or.inr hm
    · exact absurd ha h

end IUT.EllipticCurve
