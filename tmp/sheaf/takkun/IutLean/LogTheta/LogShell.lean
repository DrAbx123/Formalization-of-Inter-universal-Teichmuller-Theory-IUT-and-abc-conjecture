import Mathlib

/-!
# 対数殻 (Log-shell) と対数リンク (Log-link)

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§8 (対数殻), §9 (対数リンク) / [IUT-III] Def 1.1。

**対数殻** `I`(object (a))は、単数 `O×µ` を対数写像で加法的に解釈して得られる
コンパクトな加法的「入れ物」であり、object (b) `q_E^N` と (c) 数体を収納する。
具体的には `I_v ⊆ (k)+` で `I_v ⊗_ℤ ℚ = (k)+`、正則的整構造 `(O_Fv)+` を含む。

**対数リンク** `log : †S → ‡S` は、一方の Hodge 劇場の単数モノイド `O×µ` を、対数写像
`O×µ → (F̄_v)+` を通じて次の Hodge 劇場の対数殻へ送る結び付きである。
-/

namespace IUT.LogTheta

universe u

/-- **対数殻** (log-shell, object (a))。単数を対数写像で加法的に解釈して得られる
コンパクトな加法的加群 `I`。ここでは台となる加法群 `carrier` を記録する。 -/
structure LogShell where
  /-- 対数殻の台となる加法群 `I`。 -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]

attribute [instance] LogShell.addCommGroup

/-- **対数リンク** (log-link, Hoshi §9, §26)。単数モノイド `O×µ`(乗法群 `U`)を、
対数写像によって対数殻 `S` へ加法的に送る。`Additive U`(`U` の加法化)からの加法群準同型
として記録する ―― 対数写像が乗法を加法へ移すことの表現。 -/
structure LogLink (U : Type u) [CommGroup U] (S : LogShell) where
  /-- 対数写像 `O×µ → I`(乗法 → 加法)。 -/
  logMap : Additive U →+ S.carrier

namespace LogLink

variable {U : Type u} [CommGroup U] {S : LogShell} (L : LogLink U S)

/-- 単位元(乗法)は対数殻の零(加法)へ送られる: `log 1 = 0`。 -/
@[simp] theorem logMap_one : L.logMap (Additive.ofMul 1) = 0 := by
  simp

/-- 積の対数は対数の和: `log(a·b) = log a + log b`。 -/
theorem logMap_mul (a b : U) :
    L.logMap (Additive.ofMul (a * b))
      = L.logMap (Additive.ofMul a) + L.logMap (Additive.ofMul b) :=
  map_add L.logMap (Additive.ofMul a) (Additive.ofMul b)

end LogLink

/-! ## 対数リンク鎖 ― log-theta-lattice の縦方向(対数リンク方向) -/

/-- **対数リンク鎖**: `ℤ` で添字付けられた(単数モノイド `O×µ` + 対数殻 `I`)の族と、隣接レベルを
結ぶ対数リンク `log : O×µ_m → I_{m+1}` の鎖。[IUT-III] の **log-theta-lattice の縦方向**
(対数リンク方向)の骨格 ―― 各 Hodge 劇場の単数が次の劇場の対数殻へ対数写像で送られる。
Θ-link(横、正則構造に依らない)と異なり、対数リンクは**正則(環)構造に依存する**点が、
両リンクが可換でない理由(`LogTheta/Lattice.lean` 参照)。 -/
structure LogChain where
  /-- 各レベル `m` の対数殻 `I_m`。 -/
  shell : ℤ → LogShell.{u}
  /-- 各レベル `m` の単数モノイド `O×µ_m`。 -/
  unit : ℤ → Type u
  [commGroup : ∀ m, CommGroup (unit m)]
  /-- 対数リンク `log : O×µ_m → I_{m+1}`(乗法 → 加法)。 -/
  logLink : ∀ m : ℤ, LogLink (unit m) (shell (m + 1))

attribute [instance] LogChain.commGroup

namespace LogChain

variable (C : LogChain.{u})

/-- レベル `m` の対数リンクが積を和へ送る(`log(a·b) = log a + log b`)。鎖に沿った
乗法→加法の対応([IUT-III] の対数 Kummer 対応の素材)。 -/
theorem logLink_mul (m : ℤ) (a b : C.unit m) :
    (C.logLink m).logMap (Additive.ofMul (a * b))
      = (C.logLink m).logMap (Additive.ofMul a) + (C.logLink m).logMap (Additive.ofMul b) :=
  (C.logLink m).logMap_mul a b

end LogChain

/-- **自明な対数リンク鎖**(witness): すべてのレベルに自明な対数殻・単数群を置き、対数リンクを
零写像とする。対数リンク鎖の枠組みが非空であることを示す。 -/
def trivialLogChain : LogChain.{u} where
  shell _ := { carrier := PUnit }
  unit _ := PUnit
  logLink _ := { logMap := 0 }

end IUT.LogTheta
