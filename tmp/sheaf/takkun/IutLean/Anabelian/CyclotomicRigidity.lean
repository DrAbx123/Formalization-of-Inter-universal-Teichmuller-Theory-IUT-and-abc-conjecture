import Mathlib
import tmp.sheaf.takkun.IutLean.Foundations.Cyclotome
import tmp.sheaf.takkun.IutLean.Anabelian.FundamentalSequence
import tmp.sheaf.takkun.IutLean.Cohomology.Synchronization

/-!
# 円分剛性同型の枠組み (Cyclotomic rigidity)

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§1「円分物」, §2。

遠アーベル幾何の「群論的枠組み」では、円分物 `Ẑ(1)` の間の同一視は自明には存在せず、
群論的データの間の同型から円分物の作用を**同期**させる正準的同型 ―― 円分同期化同型 /
円分剛性同型 ―― の存在が非自明な定理となる (Hoshi §1)。

ここでは、`G` 作用付き円分物 (`GaloisCyclotome`) と、その間の `G`-同変同型 (`RigidityIso`) を
定義し、剛性同型が**亜群 (groupoid)** をなすこと(恒等・逆・合成)と、剛性同型が `G` 作用
(円分指標)を**輸送**することを証明する。正準的な同期化同型の*存在*そのものは、曲線の
基本類 `H²(Q,Ẑ) ≅ Ẑ` と連続群コホモロジーを要するため、`CyclotomicSynchronizationExists`
として保留する ([cf. SORRY_LEDGER.md])。
-/

namespace IUT.Anabelian

universe u v w

/-- **Galois 円分物**: 基底環 `R`(道徳的には `R = Ẑ`)上の円分物 `M` に、群 `G` が
`R`-線型自己同型で作用しているもの(`ρ` は道徳的には円分指標 `G → Ẑˣ`)。 -/
structure GaloisCyclotome (R : Type u) [CommRing R] (G : Type v) [Group G] where
  /-- 台となる加群。 -/
  M : Type w
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  /-- `M` は `R` 上の円分物(階数 1 自由加群)。 -/
  isCyclotome : IsCyclotome R M
  /-- `G` の `M` への `R`-線型作用(円分指標)。 -/
  ρ : G →* (M ≃ₗ[R] M)

attribute [instance] GaloisCyclotome.addCommGroup GaloisCyclotome.module

namespace GaloisCyclotome

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- **円分剛性同型 (cyclotomic rigidity isomorphism)**: 2 つの Galois 円分物の間の
`G`-同変な `R`-線型同型。円分物の間の「正準的な同一視」の抽象。 -/
structure RigidityIso (C C' : GaloisCyclotome.{u, v, w} R G) where
  /-- 台となる `R`-線型同型。 -/
  toLinearEquiv : C.M ≃ₗ[R] C'.M
  /-- `G`-同変性: 作用と可換。 -/
  equivariant : ∀ (g : G) (m : C.M),
    toLinearEquiv (C.ρ g m) = C'.ρ g (toLinearEquiv m)

namespace RigidityIso

variable {C C' C'' : GaloisCyclotome.{u, v, w} R G}

/-- 恒等円分剛性同型。 -/
def refl (C : GaloisCyclotome.{u, v, w} R G) : RigidityIso C C where
  toLinearEquiv := LinearEquiv.refl R C.M
  equivariant := fun _ _ => rfl

/-- 円分剛性同型の逆。 -/
def symm (f : RigidityIso C C') : RigidityIso C' C where
  toLinearEquiv := f.toLinearEquiv.symm
  equivariant := fun g m => by
    have h := f.equivariant g (f.toLinearEquiv.symm m)
    simp only [LinearEquiv.apply_symm_apply] at h
    rw [← h, LinearEquiv.symm_apply_apply]

/-- 円分剛性同型の合成。 -/
def trans (f : RigidityIso C C') (h : RigidityIso C' C'') : RigidityIso C C'' where
  toLinearEquiv := f.toLinearEquiv.trans h.toLinearEquiv
  equivariant := fun g m => by
    simp only [LinearEquiv.trans_apply]
    rw [f.equivariant, h.equivariant]

/-- **構造輸送 (transport)**: 円分剛性同型 `f : C ≅ C'` は `G` 作用(円分指標)を
一方から他方へ輸送する。これが「円分同期化」の内容 ―― 群論的設定の間の同型から、
円分物の作用が同期する。 -/
theorem transport (f : RigidityIso C C') (g : G) (m : C.M) :
    C'.ρ g (f.toLinearEquiv m) = f.toLinearEquiv (C.ρ g m) :=
  (f.equivariant g m).symm

end RigidityIso

end GaloisCyclotome

/-- **円分同期化同型の存在**(Hoshi §1)。旧 `opaque` を、連続第 2 群コホモロジー
(`IutLean.Cohomology`)を用いた**具体的述語**に置換した ―― 算術的基本群完全列 `S` の
Galois 商 `G`(位相群)が円分物 `Λ` に連続作用するとき、群論的に再構成される**エタール的
円分物** `H²(G,Λ)` と `Λ` の間の **基本類** `H²(G,Λ) ≅ Λ`(曲線の基本類 `H²(Q,Ẑ)≅Ẑ`、
局所類体論 / Poincaré 双対に相当)が存在すること。

**これは恒真ではない**(一般に `H²(G,Λ) ≇ Λ`):円分剛性の唯一の深い算術的入力 = 基本類の
存在を、形式化済みの連続コホモロジーで精密に表す。基本類が与えられれば円分同期化同型の構成
そのものは `IUT.Cohomology.synchronization_of_fundamentalClass`(同期化の存在)および
`synchronization_equivariant`(`G` 作用 = 円分指標の同期)で `sorry` 無しに証明される。
すなわち vague な opaque は「基本類 `H²(G,Λ)≅Λ` の存在」という一点に honest に還元された。 -/
def CyclotomicSynchronizationExists
    {Δ P G : Type u} [Group Δ] [Group P] [Group G]
    [TopologicalSpace G] [ContinuousMul G]
    (_S : ArithFundSeq Δ P G)
    (Λ : Type u) [AddCommGroup Λ] [TopologicalSpace Λ] [IsTopologicalAddGroup Λ]
    [DistribMulAction G Λ] [ContinuousSMul G Λ] : Prop :=
  Nonempty (IUT.Cohomology.FundamentalClass G Λ)

end IUT.Anabelian
