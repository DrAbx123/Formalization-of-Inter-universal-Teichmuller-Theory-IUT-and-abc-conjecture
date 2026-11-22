import Mathlib
import tmp.sheaf.takkun.IutLean.Frobenioid.Basic
import tmp.sheaf.takkun.IutLean.Cyclotome.Frobenius
import tmp.sheaf.takkun.IutLean.Theta.ThetaValues

/-!
# プライム縞の系 (Prime-strip systems) — 大規模インフラ第一層

底本: [IUT-I] §3–§6 (特に Def 5.2), [IUT-II] §4, 星裕一郎入門 §6, §8, §27 / [FrdI], [AbsTopIII]。

IUT2〜4 を精読した結果、Hodge 劇場と Θ-link の骨格は **プライム縞** (prime strip) ―― 各素点
`v ∈ V` に局所データを割り当てる族 ―― であることが核心と判明した([IUT-II] Theorem A の
`F⊩`-プライム縞(定数/テータ/Gaussian)、[IUT-III] の log-theta-lattice)。本モジュールは、
その faithful な型を [IUT-I] Definition 5.2 に基づき一から構築する:

* **D-プライム縞** (`DPrimeStrip`, エタール的/正則的): 各素点に算術的基本群 `Π_v` と
  Galois 群 `G_v`、全射 `Π_v ↠ G_v`。局所「算術的正則構造」(holomorphic) を担う群論的データ。
* **モノ解析化** (`monoAnalytic`, `D ⊢`): 正則構造を忘れ `G_v` のみを取り出した族
  (mono-analytic core の素材)。
* **F-プライム縞** (`FPrimeStrip`, Frobenius 的): D-プライム縞に、各素点の局所単項式
  `O▷_v`(`LocalMonoid`)と `Π_v`-作用を付したもの。`O▷_v` の monoid が Frobenius-like 構造。
* **忘却関手** `F → D`(単項式を忘れエタール的部分へ)。

これは `HasPrimeStripSystem`(Hodge 劇場の素点縞系)を将来 honest に具体化するための基盤。
本層では型と基本的な関手(モノ解析化・忘却)を定め、テータ/Gaussian 変種・対称化同型・
Θ×μ-link は後続層で重ねる。
-/

namespace IUT.Frobenioid

universe u

variable (V : Type*)

/-- **D-プライム縞** ([IUT-I] Def 5.2): 各素点 `v ∈ V` に局所「算術的正則構造」=
算術的基本群 `Π_v`、絶対 Galois 群 `G_v`、自然な全射 `Π_v ↠ G_v` を割り当てる族。
エタール的(群論的)データ。 -/
structure DPrimeStrip where
  /-- 各素点の算術的基本群 `Π_v`。 -/
  Pi : V → Type u
  [groupPi : ∀ v, Group (Pi v)]
  /-- 各素点の絶対 Galois 群 `G_v`。 -/
  G : V → Type u
  [groupG : ∀ v, Group (G v)]
  /-- 自然な射影 `Π_v ↠ G_v`(算術的基本群完全列の Galois 商)。 -/
  proj : ∀ v, Pi v →* G v
  /-- 射影は全射。 -/
  proj_surjective : ∀ v, Function.Surjective (proj v)

attribute [instance] DPrimeStrip.groupPi DPrimeStrip.groupG

namespace DPrimeStrip

variable {V}

/-- **モノ解析化** (`D ⊢`-プライム縞, [IUT-I] §I3): 各素点の Galois 群 `G_v` のみを取り出した
族。正則構造(`Π_v`)を忘れた「モノ解析的」データ ―― mono-analytic core の素材。 -/
abbrev monoAnalytic (D : DPrimeStrip.{u} V) : V → Type u := D.G

@[simp] theorem monoAnalytic_apply (D : DPrimeStrip.{u} V) (v : V) :
    D.monoAnalytic v = D.G v := rfl

/-- 各素点の幾何学的部分(射影の核)`Δ_v = ker(Π_v ↠ G_v)`。 -/
def geometric (D : DPrimeStrip.{u} V) (v : V) : Subgroup (D.Pi v) := (D.proj v).ker

end DPrimeStrip

/-- **F-プライム縞** ([IUT-I] Def 5.2): D-プライム縞に、各素点の局所単項式 `O▷_v`
(`CommMonoid`、Frobenius 的データ)と算術的基本群 `Π_v` の作用を付したもの。
`O▷_v` の monoid 構造が「Frobenius-like」な貼り合わせ(Θ-link)の素材。 -/
structure FPrimeStrip extends DPrimeStrip V where
  /-- 各素点の局所単項式 `O▷_{F_v}`(非零整数の乗法モノイド)。 -/
  Mon : V → Type u
  [commMonoidMon : ∀ v, CommMonoid (Mon v)]
  /-- 算術的基本群 `Π_v` の `O▷_v` への作用。 -/
  action : ∀ v, Pi v →* MulAut (Mon v)

attribute [instance] FPrimeStrip.commMonoidMon

namespace FPrimeStrip

variable {V}

/-- **忘却関手** `F → D`: F-プライム縞から、下にあるエタール的 D-プライム縞を取り出す
(局所単項式を忘れる)。 -/
def toD (F : FPrimeStrip.{u} V) : DPrimeStrip.{u} V := F.toDPrimeStrip

@[simp] theorem toD_proj (F : FPrimeStrip.{u} V) (v : V) : F.toD.proj v = F.proj v := rfl

/-- F-プライム縞のモノ解析化(`F → D → D⊢`)。 -/
def monoAnalytic (F : FPrimeStrip.{u} V) : V → Type u := F.toD.monoAnalytic

end FPrimeStrip

variable {V}

/-! ## プライム縞の同型(亜群)― 対称化同型・Θ-link の素材

素点 `V` を固定したままの D-プライム縞の同型(各素点での群同型で射影と両立)。素点の置換を
伴わないので依存型の transport を要さず、`refl`/`symm`/`trans` の亜群律を `sorry` 無しで持つ。
`F_l⋊±` 対称性による対称化同型も、Θ-link の貼り合わせも、この形(素点は固定、対象が動く)。 -/

/-- **D-プライム縞の同型**(素点固定): 各素点での群同型 `Π_v ≅ Π'_v`・`G_v ≅ G'_v` で
射影 `Π ↠ G` と両立するもの。 -/
structure DPrimeStripEquiv (D D' : DPrimeStrip.{u} V) where
  /-- 各素点での算術的基本群の同型。 -/
  isoPi : ∀ v, D.Pi v ≃* D'.Pi v
  /-- 各素点での Galois 群の同型。 -/
  isoG : ∀ v, D.G v ≃* D'.G v
  /-- 射影 `Π ↠ G` との両立性。 -/
  compat : ∀ v, (D'.proj v).comp (isoPi v).toMonoidHom = (isoG v).toMonoidHom.comp (D.proj v)

namespace DPrimeStripEquiv

/-- 両立性を関数等式として: `proj'(isoPi x) = isoG(proj x)`。 -/
theorem compat_apply {D D' : DPrimeStrip.{u} V} (φ : DPrimeStripEquiv D D') (v : V) (x : D.Pi v) :
    D'.proj v (φ.isoPi v x) = φ.isoG v (D.proj v x) :=
  DFunLike.congr_fun (φ.compat v) x

/-- 恒等同型。 -/
def refl (D : DPrimeStrip.{u} V) : DPrimeStripEquiv D D where
  isoPi v := MulEquiv.refl (D.Pi v)
  isoG v := MulEquiv.refl (D.G v)
  compat v := by ext x; rfl

/-- 逆同型。 -/
def symm {D D' : DPrimeStrip.{u} V} (φ : DPrimeStripEquiv D D') : DPrimeStripEquiv D' D where
  isoPi v := (φ.isoPi v).symm
  isoG v := (φ.isoG v).symm
  compat v := by
    ext x
    have h := φ.compat_apply v ((φ.isoPi v).symm x)
    rw [MulEquiv.apply_symm_apply] at h
    show D.proj v ((φ.isoPi v).symm x) = (φ.isoG v).symm (D'.proj v x)
    rw [h, MulEquiv.symm_apply_apply]

/-- 合成同型。 -/
def trans {D D' D'' : DPrimeStrip.{u} V} (φ : DPrimeStripEquiv D D') (ψ : DPrimeStripEquiv D' D'') :
    DPrimeStripEquiv D D'' where
  isoPi v := (φ.isoPi v).trans (ψ.isoPi v)
  isoG v := (φ.isoG v).trans (ψ.isoG v)
  compat v := by
    ext x
    show D''.proj v (ψ.isoPi v (φ.isoPi v x)) = ψ.isoG v (φ.isoG v (D.proj v x))
    rw [ψ.compat_apply v (φ.isoPi v x), φ.compat_apply v x]

/-- 同型はモノ解析的部分(`G_v` の族)の同型を誘導する: Θ-link / 対称化のモノ解析的核。 -/
def toMonoAnalyticEquiv {D D' : DPrimeStrip.{u} V} (φ : DPrimeStripEquiv D D') (v : V) :
    D.monoAnalytic v ≃* D'.monoAnalytic v :=
  φ.isoG v

end DPrimeStripEquiv

/-! ## モノ解析的プライム縞 `D⊢`(mono-analytic core)― coricity の核 -/

/-- **D⊢-プライム縞**(モノ解析的核): 各素点に絶対 Galois 群 `G_v` のみを持つ族。
正則構造(`Π_v`)を捨象した「モノ解析的」データ。[IUT-II] Theorem B の不変核
`(−)D⊢_△` ―― log-theta-lattice の全 spoke で共通の **mono-analytic core**(coricity)。 -/
structure DhPrimeStrip (V : Type*) where
  /-- 各素点の絶対 Galois 群 `G_v`。 -/
  G : V → Type u
  [group : ∀ v, Group (G v)]

attribute [instance] DhPrimeStrip.group

/-- **モノ解析化関手** `D → D⊢`: D-プライム縞から正則構造 `Π_v` を忘れ、Galois 核 `G_v` のみを残す。 -/
def DPrimeStrip.toDh (D : DPrimeStrip.{u} V) : DhPrimeStrip.{u} V where
  G := D.G

/-- D⊢-プライム縞の同型(各素点の Galois 群の同型)。 -/
structure DhPrimeStripEquiv (D D' : DhPrimeStrip.{u} V) where
  /-- 各素点での Galois 群の同型。 -/
  isoG : ∀ v, D.G v ≃* D'.G v

namespace DhPrimeStripEquiv

/-- 恒等。 -/
def refl (D : DhPrimeStrip.{u} V) : DhPrimeStripEquiv D D := ⟨fun v => MulEquiv.refl _⟩

/-- 逆。 -/
def symm {D D' : DhPrimeStrip.{u} V} (φ : DhPrimeStripEquiv D D') : DhPrimeStripEquiv D' D :=
  ⟨fun v => (φ.isoG v).symm⟩

/-- 合成。 -/
def trans {D D' D'' : DhPrimeStrip.{u} V} (φ : DhPrimeStripEquiv D D')
    (ψ : DhPrimeStripEquiv D' D'') : DhPrimeStripEquiv D D'' :=
  ⟨fun v => (φ.isoG v).trans (ψ.isoG v)⟩

end DhPrimeStripEquiv

/-- **モノ解析化の関手性**: D-プライム縞の同型は、モノ解析化 `D⊢` の同型を誘導する。 -/
def DPrimeStripEquiv.toDh {D D' : DPrimeStrip.{u} V} (φ : DPrimeStripEquiv D D') :
    DhPrimeStripEquiv D.toDh D'.toDh :=
  ⟨φ.isoG⟩

/-! ## F⊢-プライム縞(モノ解析的 Frobenius 的データ)

`D⊢`(Galois 核 `G_v`)に、各素点の局所単項式 `O×_v × q_v^ℕ`(単数と `q`-parameter の冪)と
`G_v`-作用を付したもの。Θ-link はこの `F⊢×μ`(単数 mod 根)portion の poly-同型として与えられる。 -/

/-- **F⊢-プライム縞** ([IUT-I] Def 5.2 のモノ解析的版): `D⊢` に局所単項式 `Mon_v`(`= O×_v × q_v^ℕ`)
と `G_v`-作用を付したもの。 -/
structure FhPrimeStrip (V : Type*) extends DhPrimeStrip V where
  /-- 各素点の局所単項式 `O×_v × q_v^ℕ`(モノ解析的 Frobenius 的データ)。 -/
  Mon : V → Type u
  [commMonoidMon : ∀ v, CommMonoid (Mon v)]
  /-- Galois 群 `G_v` の `Mon_v` への作用。 -/
  action : ∀ v, G v →* MulAut (Mon v)

attribute [instance] FhPrimeStrip.commMonoidMon

/-- **F⊢-プライム縞の同型**: 各素点で Galois 群の同型 `G_v ≅ G'_v` と単項式の同型
`Mon_v ≅ Mon'_v` が、`G_v`-作用と両立(同変)するもの。Θ-link はこの形(モノ解析的・同変)。 -/
structure FhPrimeStripEquiv (F F' : FhPrimeStrip.{u} V) where
  /-- 各素点での Galois 群の同型。 -/
  isoG : ∀ v, F.G v ≃* F'.G v
  /-- 各素点での単項式の同型。 -/
  isoMon : ∀ v, F.Mon v ≃* F'.Mon v
  /-- 作用との両立(同変性): `isoMon` は `G_v`-作用を `isoG` で輸送する。 -/
  compat : ∀ v g x, isoMon v (F.action v g x) = F'.action v (isoG v g) (isoMon v x)

namespace FhPrimeStripEquiv

/-- 恒等。 -/
def refl (F : FhPrimeStrip.{u} V) : FhPrimeStripEquiv F F where
  isoG v := MulEquiv.refl _
  isoMon v := MulEquiv.refl _
  compat v g x := rfl

/-- 逆。 -/
def symm {F F' : FhPrimeStrip.{u} V} (φ : FhPrimeStripEquiv F F') : FhPrimeStripEquiv F' F where
  isoG v := (φ.isoG v).symm
  isoMon v := (φ.isoMon v).symm
  compat v g y := by
    have h := φ.compat v ((φ.isoG v).symm g) ((φ.isoMon v).symm y)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    rw [← h, MulEquiv.symm_apply_apply]

/-- 合成。 -/
def trans {F F' F'' : FhPrimeStrip.{u} V} (φ : FhPrimeStripEquiv F F')
    (ψ : FhPrimeStripEquiv F' F'') : FhPrimeStripEquiv F F'' where
  isoG v := (φ.isoG v).trans (ψ.isoG v)
  isoMon v := (φ.isoMon v).trans (ψ.isoMon v)
  compat v g x := by
    show ψ.isoMon v (φ.isoMon v (F.action v g x))
        = F''.action v (ψ.isoG v (φ.isoG v g)) (ψ.isoMon v (φ.isoMon v x))
    rw [φ.compat v g x, ψ.compat v (φ.isoG v g) (φ.isoMon v x)]

/-- F⊢-プライム縞の同型は、下の `D⊢`(Galois 核)の同型を与える。 -/
def toDhEquiv {F F' : FhPrimeStrip.{u} V} (φ : FhPrimeStripEquiv F F') :
    DhPrimeStripEquiv F.toDhPrimeStrip F'.toDhPrimeStrip :=
  ⟨φ.isoG⟩

end FhPrimeStripEquiv

/-! ## Kummer 理論の核 ― 単項式の Frobenius 的円分物への Galois 作用

[IUT-II] の中心テーマ ―― **Kummer 理論**(Frobenius 的[monoid]と エタール的[Galois]を結ぶ)―― を、
私が構築した `IUT.Cyclotome.FrobeniusCyclotome`(`Λ(M) = lim μ_n(M)`、Tate 加群)および
`cyclotomicChar`(円分指標)とプライム縞インフラとで接続する。 -/

open IUT.Cyclotome in
/-- F⊢-プライム縞の各素点の単項式 `Mon_v` から定まる **Frobenius 的円分物** `Λ(Mon_v)`。 -/
abbrev FhPrimeStrip.cyclotome (F : FhPrimeStrip.{u} V) (v : V) : Type _ :=
  FrobeniusCyclotome (F.Mon v)

open IUT.Cyclotome in
/-- **Kummer 的 Galois 作用(円分指標)**: F⊢-プライム縞の Galois 群 `G_v` の単項式 `Mon_v` への
作用は、その Frobenius 的円分物 `Λ(Mon_v)` への **円分指標による作用**を誘導する。これが
Frobenius 的(monoid)と エタール的(Galois)を結ぶ **Kummer 理論**の核 ―― 局所単項式の
Galois 作用が円分物上の Galois 作用へ正準的に持ち上がる(`cyclotomicChar` の関手性による)。 -/
noncomputable def FhPrimeStrip.cyclotomicCharacter (F : FhPrimeStrip.{u} V) (v : V) :
    F.G v →* MulAut (FrobeniusCyclotome (F.Mon v)) :=
  (cyclotomicChar (F.Mon v)).comp (F.action v)

open IUT.Cyclotome in
/-- **Kummer 接続の自然性**: F⊢-プライム縞の同型 `e : F ≅ F'` は円分指標を輸送する ―― 単項式の
同型 `isoMon` が誘導する円分物の写像 `Λ(Mon_v) → Λ(Mon'_v)`(`map`)は、両者の円分指標
(`cyclotomicCharacter`)を `isoG` で対応させる。`cyclotomicChar` の関手性(`cyclotomicChar_naturality`)
と作用同変性(`FhPrimeStripEquiv.compat`)から従う ―― Kummer 理論が同型のもとで正準的に
振る舞うこと(IUT2 の Frobenius 的 ↔ エタール的の対応が同型と両立)。 -/
theorem FhPrimeStrip.cyclotomicCharacter_naturality {F F' : FhPrimeStrip.{u} V}
    (e : FhPrimeStripEquiv F F') (v : V) (g : F.G v) :
    (map (F.Mon v) (e.isoMon v).toMonoidHom).comp (F.cyclotomicCharacter v g).toMonoidHom
      = (F'.cyclotomicCharacter v (e.isoG v g)).toMonoidHom.comp
          (map (F.Mon v) (e.isoMon v).toMonoidHom) :=
  cyclotomicChar_naturality (F.Mon v) (e.isoMon v).toMonoidHom (F.action v g)
    (F'.action v (e.isoG v g)) (by ext x; exact e.compat v g x)

/-! ## Gaussian テータ値 ― プライム縞の単項式上の Gauss 分布 `q^{j²}` -/

open IUT.Theta in
/-- **Gaussian テータ値**: F⊢-プライム縞の素点 `v` で q-parameter `q ∈ Mon_v` を指定したときの
テータ値 `q^{j²} ∈ Mon_v`(Gauss 分布、[IUT-II]/[IUT-III] の Gaussian 単項式 `F⊩_gau` の核)。 -/
def FhPrimeStrip.gaussianValue (F : FhPrimeStrip.{u} V) {v : V} (q : F.Mon v) (j : ℤ) : F.Mon v :=
  thetaValueMon q j

open IUT.Theta in
/-- **Gaussian テータ値の `±1` 対称性**: `q^{(-j)²} = q^{j²}`。ゆえにプライム縞上のテータ値は
`F_l^×/{±1} ≅ LabCusp` でラベル付けされる(Gauss 分布の `±1` 対称性 = IUT のラベル理論、
Hoshi §18, §27、`Combinatorics/Fl.lean` の `LabCusp` と接続)。 -/
@[simp] theorem FhPrimeStrip.gaussianValue_neg (F : FhPrimeStrip.{u} V) {v : V}
    (q : F.Mon v) (j : ℤ) : F.gaussianValue q (-j) = F.gaussianValue q j :=
  thetaValueMon_neg q j

/-- **Gaussian プライム縞** (`F⊩_gau`, [IUT-II]/[IUT-III]): F⊢-プライム縞に各素点の
q-parameter `q_v ∈ Mon_v` を付したもの。各ラベル `j` でテータ値 `q_v^{j²}` を担う
―― Hodge-Arakelov 評価における Gauss 分布の値の「入れ物」。 -/
structure GaussianPrimeStrip (V : Type*) extends FhPrimeStrip V where
  /-- 各素点の q-parameter `q_v ∈ Mon_v`(テータ値 `q_v^{j²}` の底)。 -/
  qParam : ∀ v, Mon v

namespace GaussianPrimeStrip

/-- 素点 `v`・ラベル `j` におけるテータ値 `q_v^{j²} ∈ Mon_v`。 -/
def thetaValueAt (G : GaussianPrimeStrip V) (v : V) (j : ℤ) : G.Mon v :=
  G.toFhPrimeStrip.gaussianValue (G.qParam v) j

/-- **テータ値の `±1` 対称性**: `q_v^{(-j)²} = q_v^{j²}`(`F_l^×/{±1} ≅ LabCusp` ラベル付け)。 -/
@[simp] theorem thetaValueAt_neg (G : GaussianPrimeStrip V) (v : V) (j : ℤ) :
    G.thetaValueAt v (-j) = G.thetaValueAt v j :=
  FhPrimeStrip.gaussianValue_neg _ _ _

/-- ラベル `0` でのテータ値は `1`(正規化 `θ(ξ_0) = 1`)。 -/
@[simp] theorem thetaValueAt_zero (G : GaussianPrimeStrip V) (v : V) :
    G.thetaValueAt v 0 = 1 := by
  simp [thetaValueAt, FhPrimeStrip.gaussianValue]

end GaussianPrimeStrip

/-! ## Θ-link 鎖 ― log-theta-lattice の横方向(Θ リンク方向) -/

/-- **Θ-link 鎖**: `ℤ` で添字付けられたモノ解析的核 `D⊢` の族と、隣接する核を結ぶ Θ-link の鎖。
[IUT-III] の **log-theta-lattice の横方向**(Θ リンク方向)の骨格 ―― 隣接する Hodge 劇場が
Θ-link で結ばれ、モノ解析的核が鎖に沿って同型に保たれる(coricity)。Θ-link は正則構造ではなく
モノ解析的核 `D⊢` でのみ貼り合わせるので、鎖は `D⊢` の族として記録するのが自然。 -/
structure ThetaChain (V : Type*) where
  /-- 各 `n ∈ ℤ` におけるモノ解析的核 `D⊢`(log-theta-lattice の第 `n` 列の不変核)。 -/
  core : ℤ → DhPrimeStrip.{u} V
  /-- 隣接する核を結ぶ Θ-link。 -/
  link : ∀ n : ℤ, DhPrimeStripEquiv (core n) (core (n + 1))

namespace ThetaChain

/-- 2 段の Θ-link の合成 `D⊢_n ≅ D⊢_{n+2}`(モノ解析的核 coricity の伝播)。 -/
def link2 (c : ThetaChain.{u} V) (n : ℤ) :
    DhPrimeStripEquiv (c.core n) (c.core (n + 1 + 1)) :=
  (c.link n).trans (c.link (n + 1))

/-- 起点 `0` から任意の `n` までモノ解析的核が同型(`ℤ` 帰納法で Θ-link を合成)。 -/
theorem coricity0 (c : ThetaChain.{u} V) (n : ℤ) :
    Nonempty (DhPrimeStripEquiv (c.core 0) (c.core n)) := by
  induction n using Int.induction_on with
  | zero => exact ⟨DhPrimeStripEquiv.refl _⟩
  | succ k ih => exact ih.map (fun e => e.trans (c.link (k : ℤ)))
  | pred k ih =>
      refine ih.map (fun e => e.trans ?_)
      have h : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by ring
      exact (h ▸ c.link (-(k : ℤ) - 1)).symm

/-- **coricity**([IUT-II] Theorem B の核): Θ-link 鎖の任意の 2 核は同型 ―― **モノ解析的核は
鎖全体で不変**。log-theta-lattice の mono-analytic core が全 spoke で共通であること(coricity)。 -/
theorem coricity (c : ThetaChain.{u} V) (m n : ℤ) :
    Nonempty (DhPrimeStripEquiv (c.core m) (c.core n)) := by
  obtain ⟨e1⟩ := c.coricity0 m
  obtain ⟨e2⟩ := c.coricity0 n
  exact ⟨e1.symm.trans e2⟩

end ThetaChain

/-- **定数 Θ-link 鎖**(witness): すべての位置に同じモノ解析的核を置き、Θ-link を恒等とする。
Θ-link 鎖の枠組みが非空(realizable)であることを示す。 -/
def constantThetaChain (D : DhPrimeStrip.{u} V) : ThetaChain.{u} V where
  core _ := D
  link _ := DhPrimeStripEquiv.refl D

/-! ## エタール絵 ― モノ解析的核と spoke の置換対称性([IUT-II] Theorem B(ii)) -/

/-- **エタール絵** ([IUT-II] Theorem B): モノ解析的核 `D⊢` と、それを共有する複数の **spoke**
(各 spoke は異なる「算術的正則構造」= D-プライム縞で、そのモノ解析化が共通核に一致)。
各 spoke が mono-analytic core から放射する「異なる正則構造」を表す。 -/
structure EtalePicture (V Spoke : Type*) where
  /-- 共通のモノ解析的核 `D⊢`(全 spoke で共通 = coricity)。 -/
  core : DhPrimeStrip.{u} V
  /-- 各 spoke の算術的正則構造(D-プライム縞)。 -/
  spoke : Spoke → DPrimeStrip.{u} V
  /-- 各 spoke のモノ解析化が共通核に一致(coricity)。 -/
  spokeCore : ∀ s, DhPrimeStripEquiv (spoke s).toDh core

namespace EtalePicture

/-- **spoke の置換対称性** ([IUT-II] Theorem B(ii)): 任意の spoke の置換 `σ` はエタール絵を保つ
―― 共通核は不変、spoke のみ `σ` で並べ替えられる。エタール絵が spoke の任意の置換対称性を
持つこと(mono-analytic core が置換不変であることの帰結)。 -/
def permute {V Spoke : Type*} (E : EtalePicture.{u} V Spoke) (σ : Spoke ≃ Spoke) :
    EtalePicture.{u} V Spoke where
  core := E.core
  spoke s := E.spoke (σ s)
  spokeCore s := E.spokeCore (σ s)

/-- 置換対称性のもとで**モノ解析的核は不変**(coricity = 置換対称性の核)。 -/
@[simp] theorem permute_core {V Spoke : Type*} (E : EtalePicture.{u} V Spoke) (σ : Spoke ≃ Spoke) :
    (E.permute σ).core = E.core := rfl

end EtalePicture

/-! ## Frobenius 絵 → エタール絵(canonical splitting)-/

/-- **Frobenius 絵**(holomorphic Θ-link 鎖): `ℤ` で添字付けられた D-プライム縞(正則)の族と、
隣接する縞のモノ解析的核を結ぶ Θ-link。[IUT-II] の Frobenius-picture ―― Θ-link で結ばれた
Hodge 劇場(正則構造)の鎖。 -/
structure FrobeniusChain (V : Type*) where
  /-- 各 `n ∈ ℤ` の D-プライム縞(正則構造 = spoke)。 -/
  spoke : ℤ → DPrimeStrip.{u} V
  /-- 隣接する縞のモノ解析的核を結ぶ Θ-link。 -/
  link : ∀ n : ℤ, DhPrimeStripEquiv (spoke n).toDh (spoke (n + 1)).toDh

namespace FrobeniusChain

/-- Frobenius 絵の下部にあるモノ解析的核の Θ-link 鎖。 -/
def toThetaChain (c : FrobeniusChain.{u} V) : ThetaChain.{u} V where
  core n := (c.spoke n).toDh
  link n := c.link n

/-- **canonical splitting**(Frobenius 絵 → エタール絵, [IUT-II]): Frobenius 絵(Θ-link 鎖)は、
共通のモノ解析的核(coricity で全 spoke 共通)と spoke 族からなる**エタール絵**へ分解される。
これが「Frobenius-picture の canonical splitting = étale-picture」の内容 ―― Frobenius 絵の
Θ-link を、モノ解析的核を軸とする spoke の放射(エタール絵)へ読み替える。 -/
noncomputable def toEtalePicture (c : FrobeniusChain.{u} V) : EtalePicture.{u} V ℤ where
  core := (c.spoke 0).toDh
  spoke := c.spoke
  spokeCore s := (c.toThetaChain.coricity s 0).some

end FrobeniusChain

/-- **Θ-link(の骨格)**: 2 つの F-プライム縞の**モノ解析的核 `D⊢` のみ**を同一視する貼り合わせ
([IUT-II] Theorem A (iii) の `Θ×μ`-link、`F⊩×μ_env ≅ F⊩×μ_△` の poly-同型に対応)。
正則構造(`Π_v`・単項式)ではなくモノ解析的核(`G_v`)で貼り合わせる点が、Θ-link が
通常のスキーム論の枠外にある所以。`D⊢`-プライム縞の同型として記録する。 -/
def ThetaLink (F F' : FPrimeStrip.{u} V) : Type _ :=
  DhPrimeStripEquiv F.toD.toDh F'.toD.toDh

/-! ## ラベル付きプライム縞系(Hodge 劇場のプライム縞骨格) -/

/-- **ラベル付きプライム縞系**: ラベル集合 `L`(= `LabCusp±`/`F_l`)上の D-プライム縞の族
`strip`、対称性群 `Sym`(`F_l⋊±`/`F_l⋆`)の `L` への作用、および各対称性元が与える縞間の
**対称化同型** `strip t ≅ strip (s • t)`([IUT-II] Corollary 4.6 の symmetrizing isomorphism)。
これが Hodge 劇場の素点縞データの組合せ的骨格 ―― `HasPrimeStripSystem` の対称性両立性の核。 -/
structure LabeledPrimeStripSystem (V L Sym : Type*) [Group Sym] [MulAction Sym L] where
  /-- 各ラベルにおける D-プライム縞。 -/
  strip : L → DPrimeStrip.{u} V
  /-- 対称性元 `s` が与える対称化同型 `strip t ≅ strip (s • t)`。 -/
  symIso : ∀ (s : Sym) (t : L), DPrimeStripEquiv (strip t) (strip (s • t))

/-- **定数ラベル付き系**(witness): すべてのラベルに同じ D-プライム縞 `D` を置き、対称化同型を
恒等とする。ラベル付きプライム縞系の枠組みが非空であることを示す。 -/
def constantLabeledSystem (V L Sym : Type*) [Group Sym] [MulAction Sym L]
    (D : DPrimeStrip.{u} V) : LabeledPrimeStripSystem.{u} V L Sym where
  strip _ := D
  symIso _ _ := DPrimeStripEquiv.refl D

end IUT.Frobenioid
