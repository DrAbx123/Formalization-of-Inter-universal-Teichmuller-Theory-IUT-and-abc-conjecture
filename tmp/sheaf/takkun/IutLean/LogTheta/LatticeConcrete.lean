import tmp.sheaf.takkun.IutLean.Frobenioid.PrimeStripSystem
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell

/-!
# 具体的 log-theta-lattice ― 横(Θ-link)と縦(log-link)の統合

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§9, §26 / [IUT-III] §1。

[IUT-III] の中心装置 **log-theta-lattice** は、`ℤ × ℤ` で添字付けられた格子であり、
* **横方向**(`(n,m) → (n+1,m)`)は **Θ-link**(モノ解析的核 `D⊢` で貼り合わせ、正則構造に依らない)、
* **縦方向**(`(n,m) → (n,m+1)`)は **対数リンク**(単数 `O×µ` を対数殻 `I` へ、正則構造に依存)
で結ばれる。本質的に重要なのは、この 2 種のリンクが**可換でない**ことである。

本モジュールでは、私が構築した具体的プライム縞インフラ(`Frobenioid.PrimeStripSystem` の
`DhPrimeStrip`/`DhPrimeStripEquiv`/`ThetaChain`)と対数殻インフラ(`LogTheta.LogShell` の
`LogShell`/`LogLink`/`LogChain`)を**統合**し、`ℤ × ℤ` 上の具体的 log-theta-lattice を構成する。
各行は `ThetaChain`(横)、各列は `LogChain`(縦)に射影される。
-/

namespace IUT.LogTheta

open IUT.Frobenioid

universe u

variable (V : Type*)

/-- **具体的 log-theta-lattice**: `ℤ × ℤ` の各格子点 `(n,m)` に、モノ解析的核 `D⊢`(横の
Θ-link で結ばれる)と、単数群 `O×µ`・対数殻 `I`(縦の対数リンクで結ばれる)を置いた格子。
[IUT-III] の中心装置。横(Θ-link, 正則構造非依存)と縦(log-link, 正則構造依存)は可換でない。 -/
structure LogThetaLatticeConcrete where
  /-- 格子点 `(n,m)` のモノ解析的核 `D⊢`。 -/
  core : ℤ × ℤ → DhPrimeStrip.{u} V
  /-- 横方向の Θ-link `D⊢_{(n,m)} ≅ D⊢_{(n+1,m)}`。 -/
  thetaLink : ∀ n m : ℤ, DhPrimeStripEquiv (core (n, m)) (core (n + 1, m))
  /-- 格子点 `(n,m)` の単数群 `O×µ`。 -/
  unit : ℤ × ℤ → Type u
  [commGroup : ∀ p, CommGroup (unit p)]
  /-- 格子点 `(n,m)` の対数殻 `I`。 -/
  shell : ℤ × ℤ → LogShell.{u}
  /-- 縦方向の対数リンク `log : O×µ_{(n,m)} → I_{(n,m+1)}`。 -/
  logLink : ∀ n m : ℤ, LogLink (unit (n, m)) (shell (n, m + 1))

attribute [instance] LogThetaLatticeConcrete.commGroup

namespace LogThetaLatticeConcrete

variable {V} (L : LogThetaLatticeConcrete.{u} V)

/-- **第 `m` 行 = Θ-link 鎖(横方向)**: モノ解析的核が Θ-link で結ばれる
([IUT-III] の log-row、`LogTheta/Lattice.lean` の `logRow` のモノ解析的版)。 -/
def thetaRow (m : ℤ) : ThetaChain.{u} V where
  core n := L.core (n, m)
  link n := L.thetaLink n m

/-- **第 `n` 列 = 対数リンク鎖(縦方向)**: 単数・対数殻が対数リンクで結ばれる
([IUT-III] の Θ-column、`LogTheta/Lattice.lean` の `thetaColumn` の対数版)。 -/
def logColumn (n : ℤ) : LogChain.{u} where
  shell m := L.shell (n, m)
  unit m := L.unit (n, m)
  logLink m := L.logLink n m

@[simp] theorem thetaRow_core (m n : ℤ) : (L.thetaRow m).core n = L.core (n, m) := rfl

@[simp] theorem logColumn_shell (n m : ℤ) : (L.logColumn n).shell m = L.shell (n, m) := rfl

end LogThetaLatticeConcrete

/-- **自明な log-theta-lattice**(witness): すべての格子点に自明な核・単数群・対数殻を置き、
両リンクを恒等/零とする。具体的 log-theta-lattice の枠組みが非空であることを示す。 -/
def trivialLogThetaLattice : LogThetaLatticeConcrete.{u} V where
  core _ := { G := fun _ => PUnit }
  thetaLink _ _ := DhPrimeStripEquiv.refl _
  unit _ := PUnit
  shell _ := { carrier := PUnit }
  logLink _ _ := { logMap := 0 }

end IUT.LogTheta
