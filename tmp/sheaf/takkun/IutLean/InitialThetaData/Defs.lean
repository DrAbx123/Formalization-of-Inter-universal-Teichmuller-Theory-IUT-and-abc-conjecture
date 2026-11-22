import tmp.sheaf.takkun.IutLean.Combinatorics.Fl
import tmp.sheaf.takkun.IutLean.InitialThetaData.Deferred
import tmp.sheaf.takkun.IutLean.Anabelian.CoreData
import tmp.sheaf.takkun.IutLean.NumberTheory.Places
import tmp.sheaf.takkun.IutLean.NumberTheory.PlaceLocalization
import tmp.sheaf.takkun.IutLean.EllipticCurve.Torsion
import tmp.sheaf.takkun.IutLean.EllipticCurve.FieldOfModuli
import tmp.sheaf.takkun.IutLean.EllipticCurve.GaloisRep

/-!
# 初期 Θ データ (Initial Θ-data) — [IUT-I], Definition 3.1 / Hoshi §17

宇宙際 Teichmüller 理論の**出発点**となる 7 つ組
`(F/F̄, X_F, l, C_K, V, V^bad_mod, ε)`。

Mathlib で**今表現できる部分**(数体 `F`、`√-1 ∈ F`、Weierstrass 楕円曲線 `E`、素数 `l ≥ 5`)は
具体的な構造体フィールドとして、**未だ形式化されていない幾何学的・遠アーベル的条件**
(安定還元・`SL₂` 像・モジュライ体・`K`-core・付値の切断など, Def 3.1 (b)–(e))は
`IutLean/InitialThetaData/Deferred.lean` の `opaque` 述語を要求するフィールドとして束ねる。

これにより「初期 Θ データ」という概念が Lean の型として存在し、その上に Hodge 劇場
(Phase 6 以降)を構築できる。未証明の葉は `Deferred.lean` に局在する。
-/

open scoped NumberField

namespace IUT

universe u

/-- `√-1 ∈ F`、すなわち `i² = -1` を満たす元 `i ∈ F` が存在する ([IUT-I] Def 3.1 (a))。 -/
def HasSqrtNegOne (F : Type u) [Field F] : Prop := ∃ i : F, i * i = -1

/-- **初期 Θ データ** ([IUT-I], Definition 3.1 / Hoshi §17)。

7 つ組 `(F/F̄, X_F, l, C_K, V, V^bad_mod, ε)` を束ねた構造体。
条件 (a),(c) の数体・素数に関わる部分は具体的に、(b),(d),(e) の幾何学的・遠アーベル的
条件は `Deferred.lean` の `opaque` 述語として要求する。 -/
structure InitialThetaData where
  /-- 数体 `F`(条件 (a))。`F̄` はその代数閉包、`G_F = Gal(F̄/F)`。 -/
  F : Type u
  [field : Field F]
  [numberField : NumberField F]
  [decidableEq : DecidableEq F]
  /-- **(a)** `√-1 ∈ F`。 -/
  sqrt_neg_one : HasSqrtNegOne F
  /-- **(b)** 楕円曲線 `E = E_F`(Weierstrass モデル)。穴あき楕円曲線 `X_F = E_F ∖ {O}` を定める。 -/
  E : WeierstrassCurve F
  /-- `E` が実際に楕円曲線(判別式が単元)であること。 -/
  [E_elliptic : E.IsElliptic]
  /-- **(c)** 素数 `l`。 -/
  l : ℕ
  /-- `l` は素数。 -/
  l_prime : Nat.Prime l
  /-- `l ≥ 5`。 -/
  l_ge_five : 5 ≤ l
  [lNeZero : NeZero l]
  /-- **(b)** `X_F` は全非アルキメデス素点で安定還元を持つ(M5.5 で素点配線により具体化)。 -/
  stable_reduction : IUT.NumberTheory.HasStableReductionEverywhere (R := 𝓞 F) E
  /-- **(c)** `l`-等分表現の像が `SL₂(F_l)` を含む(M8 で mod-`l` Galois 表現により具体化)。 -/
  sl2_image : IUT.EllipticCurve.ContainsSL2ImageAlgClosure E l
  /-- **(b)** `F/F_mod` は `l` と素な次数の Galois 拡大(`F_mod = ℚ(j_E)`、M6 で具体化)。 -/
  galois_field_of_moduli : IUT.EllipticCurve.GaloisOverFieldOfModuli E l
  /-- **(b)** `E` の `2·3`-等分点は `F` 有理的(`|E(F)[6]| = 36`、M4 で具体化)。 -/
  six_torsion_rational : IUT.EllipticCurve.SixTorsionRational E
  /-- **(b)** bad(乗法的)還元の奇剰余標数素点が存在(`V^bad_mod ≠ ∅`、M5.6 で素点配線により具体化)。 -/
  bad_place_data : IUT.NumberTheory.HasBadPlaceData (R := 𝓞 F) E
  /-- **(d)** `C_K = C_F ×_F K` は `K`-core(型 `(1, l-tors)±`)。旧 `opaque IsKCore` は
  `Anabelian/CoreData.lean` の**具体的データ構造 `KCoreData`** に置換された ―― `Loc_K(C_K)` 圏・
  対象 `C_K`/`X_K`・被覆・忠実な `F_l⋊±` デッキ作用・**終対象性 = K-core 性**(`IsCore`)を
  データとして保持する(`MonoThetaEnvironment.thetaGroup`/`PrimeStripSystem` と同じ honest
  データパターン)。`E` の幾何からのインスタンス供給(実際の被覆圏の構成)は将来課題。 -/
  coreData : Anabelian.KCoreData l
  /-- **(b)** モジュライ体 `F_mod ⊆ F`([IUT-I] Def 3.1(b))。数体。 -/
  Fmod : Type u
  [fieldFmod : Field Fmod]
  [numberFieldFmod : NumberField Fmod]
  /-- **(c),(d)** `l`-等分の体 `K = K(E[l])`。`F_mod` 上の(有限次)数体拡大。 -/
  Kl : Type u
  [fieldKl : Field Kl]
  [numberFieldKl : NumberField Kl]
  [algebraFmodKl : Algebra Fmod Kl]
  -- **(e)** `V ⊆ V(K)` が `V(K) ↠ V_mod` の切断であるという条件は、もはや仮定ではなく
  -- `InitialThetaData.valuationSection` で**証明される**(M2.5)。

attribute [instance] InitialThetaData.field InitialThetaData.numberField
  InitialThetaData.decidableEq InitialThetaData.lNeZero
  InitialThetaData.E_elliptic InitialThetaData.fieldFmod InitialThetaData.numberFieldFmod
  InitialThetaData.fieldKl InitialThetaData.numberFieldKl InitialThetaData.algebraFmodKl

namespace InitialThetaData

variable (D : InitialThetaData)

/-- 素数 `l` は奇数(`l ≥ 5` より)。 -/
theorem l_odd : Odd D.l := D.l_prime.odd_of_ne_two (by have := D.l_ge_five; omega)

/-- `l⋆ = (l-1)/2` の関係式 `2·l⋆ + 1 = l`。 -/
theorem two_mul_lStar_add_one : 2 * lStar D.l + 1 = D.l :=
  IUT.two_mul_lStar_add_one D.l D.l_odd

/-- `l` を `F_l` 組合せ論の API で使うための `Fact`(`D` から導出)。 -/
theorem fact_prime : Fact (Nat.Prime D.l) := ⟨D.l_prime⟩

/-- **[IUT-I] Def 3.1(e) は自動的に成立**(M2.5)。`K/F_mod` が数体拡大ゆえ、素点制限
`V(K) ↠ V_mod` は lying-over で全射、よって切断を持ち `V ≅ V_mod`。
旧 `opaque` 条件 `valuation_section` を、**証明された定理**に置換した。 -/
theorem valuationSection : IUT.NumberTheory.HasValuationSection D.Fmod D.Kl :=
  IUT.NumberTheory.hasValuationSection D.Fmod D.Kl

end InitialThetaData

end IUT
