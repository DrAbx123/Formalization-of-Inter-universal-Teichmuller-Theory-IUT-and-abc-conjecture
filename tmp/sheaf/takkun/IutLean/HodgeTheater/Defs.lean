import Mathlib
import tmp.sheaf.takkun.IutLean.Combinatorics.Fl
import tmp.sheaf.takkun.IutLean.HodgeTheater.Symmetry
import tmp.sheaf.takkun.IutLean.HodgeTheater.PrimeStripData

/-!
# Hodge 劇場 (Hodge theaters) の構成

底本: [IUT-I] §4–§6, 星裕一郎入門 §20 (加法的), §25 (乗法的), §26 (貼り合わせ)。

IUT の主定理の舞台となる **Hodge 劇場** は、2 つの対称性のもとで構成される 2 種の Hodge
劇場を貼り合わせて得られる:

* **D-Θ±ell Hodge 劇場**(加法的/幾何学的, `F_l^{⋊±}` 対称性) ―― テータ関数とその代入点の
  ラベル管理、特殊値の「入れ物」のための設定 (Hoshi §20)。
* **D-ΘNF Hodge 劇場**(乗法的/数論的, `F_l^⋆` 対称性) ―― 数体の多輻的表示のための設定
  (Hoshi §25)。
* **Θ±ellNF Hodge 劇場** ―― 両者を共通の素数 `l` のもとで貼り合わせたもの (Hoshi §26)。

ここでは各 Hodge 劇場の**組合せ的骨格**(素数 `l` とその対称性、ラベル集合)を構造体として
定義する。素点縞系 (prime strips)・大域的フロベニオイド等の幾何学的データは
`HasPrimeStripSystem` として保留する ([cf. SORRY_LEDGER.md])。対称性の単純推移性
(`Symmetry.lean` で証明済み)を各 Hodge 劇場に対して再公開する。
-/

namespace IUT.HodgeTheater

open IUT

/- **旧 `opaque HasPrimeStripSystem` は解消済み**: Phase D のプライム縞インフラにより、
素点縞系は具体的データ構造 `PrimeStripSystem l`(`HodgeTheater/PrimeStripData.lean`)として
表現された ―― `F_l⋊±`/`F_l⋆` 対称化同型付きラベル付き縞系・Gaussian テータ値・モノ解析的
貼り合わせ・非退化性。テータ値の `±1` 対称性と Kummer 円分指標は**証明された帰結**として付随。
Hodge 劇場は以下でこのデータを直接**保持**する(`MonoThetaEnvironment.thetaGroup` と同じ
honest データパターン)。 -/

/-- **D-Θ±ell Hodge 劇場**(加法的/幾何学的, Hoshi §20)。
素数 `l ≥ 5` とその加法的対称性 `F_l^{⋊±} = GeoSym l`(`LabCusp± ≅ F_l` に作用)を核に持ち、
素点縞系(`F_l⋊±` 対称化同型・テータ値・貼り合わせ込みの具体的データ)を保持する。 -/
structure AdditiveHodgeTheater where
  /-- 素数 `l`。 -/
  l : ℕ
  [lPrime : Fact l.Prime]
  /-- `l ≥ 5`。 -/
  l_ge_five : 5 ≤ l
  /-- **素点縞系**(具体的データ、旧 opaque の脱ブラックボックス化)。 -/
  primeStrips : PrimeStripSystem l

/-- **D-ΘNF Hodge 劇場**(乗法的/数論的, Hoshi §25)。
素数 `l` とその乗法的対称性 `F_l^⋆ = LabCusp`(自身に左並進で作用)を核に持ち、
素点縞系(具体的データ)を保持する。 -/
structure MultiplicativeHodgeTheater where
  /-- 素数 `l`。 -/
  l : ℕ
  [lPrime : Fact l.Prime]
  /-- `l ≥ 5`。 -/
  l_ge_five : 5 ≤ l
  /-- **素点縞系**(具体的データ、旧 opaque の脱ブラックボックス化)。 -/
  primeStrips : PrimeStripSystem l

attribute [instance] AdditiveHodgeTheater.lPrime MultiplicativeHodgeTheater.lPrime

/-- **Θ±ellNF Hodge 劇場**(Hoshi §26)。加法的(幾何学的対称性)と乗法的(数論的対称性)の
Hodge 劇場を、共通の素数 `l` のもとで(対称性の出自としては非従来的な形で)貼り合わせたもの。
(`Full` = 完全な Hodge 劇場 = Θ±ellNF Hodge 劇場。) -/
structure Full where
  /-- 加法的 (D-Θ±ell) 部分。 -/
  add : AdditiveHodgeTheater
  /-- 乗法的 (D-ΘNF) 部分。 -/
  mul : MultiplicativeHodgeTheater
  /-- **貼り合わせ両立性**: 加法的・乗法的部分は共通の素数 `l` を持つ。 -/
  glue : add.l = mul.l

namespace Full

variable (H : Full)

/-- Hodge 劇場の(共通の)素数 `l`。 -/
def l : ℕ := H.add.l

instance : Fact (Nat.Prime H.l) := H.add.lPrime

theorem l_ge_five : 5 ≤ H.l := H.add.l_ge_five

/-- **加法的対称性群** `F_l^{⋊±} = GeoSym l`(位数 `2l`)、`LabCusp± ≅ F_l` に作用。 -/
abbrev addSymmetry : Type := GeoSym H.l

/-- **乗法的対称性群** `F_l^⋆ = LabCusp l`(位数 `l⋆`)、`LabCusp` に左並進で作用。 -/
abbrev mulSymmetry : Type := LabCusp H.l

/-- **加法的対称性の単純推移性**(`Symmetry.lean` の結果を Hodge 劇場へ再公開): 加法的ラベル
`F_l` 上で並進が単純推移的。 -/
theorem additive_simplyTransitive (j j' : Fl H.l) : ∃! a : Fl H.l, a + j = j' :=
  IUT.HodgeTheater.additive_simplyTransitive H.l j j'

/-- **乗法的対称性の単純推移性**(`Symmetry.lean` の結果を Hodge 劇場へ再公開): 乗法的ラベル
`LabCusp` 上で `F_l^⋆` が単純推移的。 -/
theorem multiplicative_simplyTransitive (j j' : LabCusp H.l) :
    ∃! a : LabCusp H.l, a * j = j' :=
  IUT.HodgeTheater.multiplicative_simplyTransitive H.l j j'

end Full

end IUT.HodgeTheater
