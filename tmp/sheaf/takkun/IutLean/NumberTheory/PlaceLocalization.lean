import Mathlib
import tmp.sheaf.takkun.IutLean.EllipticCurve.Reduction

/-!
# 素点配線: 局所化 DVR と全素点での安定還元 (Track A+B / [IUT-I] Def 3.1(b), M5.5)

底本: [IUT-I] Definition 3.1 (b)(`X_F` は全非アルキメデス素点で安定還元を持つ)。

Dedekind 整域 `R`(数体の整数環 `𝓞_F`)の各有限素点 `v`(`HeightOneSpectrum R`)に対し、
局所化 `R_v = R_(v)` は**離散付値環 (DVR)** であり、その分数体は `R` の分数体 `K`(= 数体 `F`)に
一致する。本ファイルでは、Mathlib の局所化理論(`localizationAlgebraOfSubmonoidLe`,
`isFractionRing_of_isDomain_of_isLocalization`, `isDiscreteValuationRing_of_dedekind_domain`)を
用いて、各素点 `v` での DVR・分数体・代数構造を**配線**し、`HasStableReductionEverywhere`
(全有限素点で安定還元 = 半安定)を**具体的命題**として与える。

これにより M5(安定還元の局所版)を全素点に量化し、Def 3.1(b) の安定還元条件を具体化する。
-/

namespace IUT.NumberTheory

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- 素点 `v` の局所化環 `R_v = R_(v)`(Dedekind 整域では DVR、分数体は `K`)。 -/
abbrev placeLocalization (v : HeightOneSpectrum R) : Type _ :=
  Localization.AtPrime v.asIdeal

/-- **[IUT-I] Def 3.1(b) の `HasStableReductionEverywhere` の具体化(素点配線, M5.5)**:
数体 `K` 上の楕円曲線 `E` が**全ての有限素点 `v` で安定還元**を持つこと。各素点 `v` の局所化
`R_v` は(Dedekind 整域ゆえ)DVR で分数体は `K`、その上で `E` が半安定(`IsSemistable`)。 -/
def HasStableReductionEverywhere (E : WeierstrassCurve K) : Prop :=
  ∀ v : HeightOneSpectrum R,
    letI algv : Algebra (placeLocalization v) K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (placeLocalization v) K
        v.asIdeal.primeCompl (nonZeroDivisors R) v.asIdeal.primeCompl_le_nonZeroDivisors
    letI : IsScalarTower R (placeLocalization v) K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (placeLocalization v) K
        v.asIdeal.primeCompl (nonZeroDivisors R) v.asIdeal.primeCompl_le_nonZeroDivisors
    letI : IsFractionRing (placeLocalization v) K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl
        (placeLocalization v) K
    haveI : v.asIdeal.IsPrime := v.isPrime
    letI : IsDiscreteValuationRing (placeLocalization v) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
        (placeLocalization v)
    IUT.EllipticCurve.IsSemistable (placeLocalization v) (W := E)

/-- **[IUT-I] Def 3.1(b) の `HasBadPlaceData` の具体化(素点配線, M5.6)**:
`E` が bad(乗法的)還元を持つ**奇剰余標数**の有限素点が(少なくとも 1 つ)存在すること。
「奇剰余標数」は `(2 : R) ∉ v.asIdeal`(2 が素点 `v` に属さない ⟺ 剰余標数が 2 でない)で表す。 -/
def HasBadPlaceData (E : WeierstrassCurve K) : Prop :=
  ∃ v : HeightOneSpectrum R,
    (2 : R) ∉ v.asIdeal ∧
    letI algv : Algebra (placeLocalization v) K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (placeLocalization v) K
        v.asIdeal.primeCompl (nonZeroDivisors R) v.asIdeal.primeCompl_le_nonZeroDivisors
    letI : IsScalarTower R (placeLocalization v) K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (placeLocalization v) K
        v.asIdeal.primeCompl (nonZeroDivisors R) v.asIdeal.primeCompl_le_nonZeroDivisors
    letI : IsFractionRing (placeLocalization v) K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl
        (placeLocalization v) K
    haveI : v.asIdeal.IsPrime := v.isPrime
    letI : IsDiscreteValuationRing (placeLocalization v) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
        (placeLocalization v)
    E.HasMultiplicativeReduction (placeLocalization v)

end IUT.NumberTheory
