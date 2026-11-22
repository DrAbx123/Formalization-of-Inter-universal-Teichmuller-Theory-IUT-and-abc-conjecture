import Mathlib

/-!
# [IUT-I] Definition 3.1 の「保留された」幾何学的・遠アーベル的条件

初期 Θ データ ([IUT-I], Def 3.1 / Hoshi §17) の条件のうち、Mathlib に未だ存在しない概念
―― 安定還元、エタール基本群、`K`-core、モジュライ体、付値の切断、`C_K` のカスプ ―― に
依存するものを、ここでは `opaque` な命題として宣言する。

これは**未証明の葉の境界を明示する台帳**である:
* 各命題の *主張* は意図された意味(docstring に記載、原論文の該当節を参照)で固定されているが、
* その *内容* は後続フェーズで該当概念を形式化した際に、この `opaque` を本来の `def` に
  置き換えることで供給される。

`SORRY_LEDGER.md`(将来導入)に対応する、Phase 2 段階での保留事項。
-/

namespace IUT

universe u

/- **[IUT-I] Def 3.1 (b)** の `HasStableReductionEverywhere`(`X_F` が全非アルキメデス素点で
安定還元)は `opaque` から解消された(M5.5, 素点配線)。
`IUT.NumberTheory.HasStableReductionEverywhere`(`NumberTheory/PlaceLocalization.lean`)で、
各素点の局所化 DVR 上の半安定性として**具体的命題**化(`∀ v, IsSemistable R_v E`)。 -/

/- **[IUT-I] Def 3.1 (c)** の `ContainsSL2Image`(`E` の `l`-等分表現 `G_F → GL₂(F_l)` の像が
`SL₂(F_l)` を含む)は `opaque` から解消された(M8, mod-`l` Galois 表現の本格構築)。
`IUT.EllipticCurve.ContainsSL2ImageAlgClosure`(`EllipticCurve/GaloisRep.lean`)で、代数閉包 `F̄` 上の
mod-`l` Galois 表現 `galoisRepMod : Gal(F̄/F) → GL(E[l])` を構成し、その像が行列式 `1` の
`F_l`-線型自己同型(= `SL₂(F_l)`)をすべて含む、という**具体的命題**として定義。 -/

/- **[IUT-I] Def 3.1 (b)** の `GaloisOverFieldOfModuli`(`F/F_mod` が `l` と素な次数の Galois 拡大)
は `opaque` から解消された(M6)。`IUT.EllipticCurve.GaloisOverFieldOfModuli`
(`EllipticCurve/FieldOfModuli.lean`)で `F_mod = ℚ(j_E)` を用いた**具体的命題**
`IsGalois ℚ(j_E) F ∧ (finrank ℚ(j_E) F).Coprime l` として定義。 -/

/- **[IUT-I] Def 3.1 (b)** の `SixTorsionRational`(`E` の `2·3`-等分点が `F` 有理的)は
`opaque` から解消された(M4)。`IUT.EllipticCurve.SixTorsionRational`(`EllipticCurve/Torsion.lean`)
で `n`-等分部分群を用いた**具体的命題** `|W(F)[6]| = 36`(完全 6-等分の `F` 有理性)として定義。 -/

/- **[IUT-I] Def 3.1 (b)** の `HasBadPlaceData`(bad 乗法的還元の奇剰余標数素点が存在)は
`opaque` から解消された(M5.6, 素点配線)。`IUT.NumberTheory.HasBadPlaceData`
(`NumberTheory/PlaceLocalization.lean`)で `∃ v, (2:R)∉v.asIdeal ∧ E.HasMultiplicativeReduction R_v`
として**具体的命題**化。 -/

/- **[IUT-I] Def 3.1 (d)** の `IsKCore`(`C_K = C_F ×_F K` が `K`-core)は `opaque` から
解消された(曲線 π₁ 基盤 / Phase E)。`IUT.Anabelian.KCoreData`(`Anabelian/CoreData.lean`)で
**具体的データ構造**化 ―― 圏 `Loc_K(C_K)`・対象 `C_K`/`X_K`・被覆 `X_K → C_K`・忠実な
`F_l⋊±` デッキ作用・**終対象性 = K-core 性**(`IsCore`、`Anabelian/Core.lean` で完全証明済みの
機構)。`Aut_K(C_K) = {1}`(Hoshi §17)とデッキ変換群の位数 `2l` は**証明される帰結**。
エタール基本群の受け皿は `Anabelian/CurvePi1.lean`(Mathlib Galois 圏による曲線 π₁ 基盤)。
`InitialThetaData.coreData` フィールドで直接データとして保持される。 -/

/- **[IUT-I] Def 3.1 (e)** は `opaque` から解消された(M2.5)。
`V ⊆ V(K)` が全射 `V(K) ↠ V_mod` の切断の像であるという条件は、`K/F_mod` が数体拡大ゆえ
**常に成立する定理** `IUT.NumberTheory.hasValuationSection`(`NumberTheory/Places.lean`)として
証明済み。`InitialThetaData.valuationSection` で初期 Θ データに対して直接得られる。 -/

end IUT
