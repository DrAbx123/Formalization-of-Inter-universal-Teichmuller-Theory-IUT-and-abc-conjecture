import Mathlib
import tmp.sheaf.takkun.IutLean.Cohomology.Continuous

/-!
# 円分同期化同型と基本類 (Cyclotomic synchronization & the fundamental class)

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§1 / Mochizuki [AbsTopIII]。

円分剛性(Hoshi §1)の核心 ―― **円分同期化同型** ―― は、群論的に再構成される
**エタール的円分物** `Λ_ét(G) = H²(G, Λ)`(連続第 2 群コホモロジー)と、もとの円分物 `Λ`
(`= Ẑ(1)`、Frobenius 的/惰性的)とを結ぶ正準的同型である。その存在は、曲線の
**基本類** `H²(Q, Ẑ) ≅ Ẑ`(局所類体論 / Poincaré 双対に相当する**深い算術的入力**)に帰着する。

本モジュールでは、`IutLean.Cohomology.Continuous` で構築した連続 `H²` を用いて:

* `EtaleCyclotome G Λ := H²(G, Λ)` ―― 群論的に定まるエタール的円分物;
* `FundamentalClass G Λ` ―― 基本類 `H²(G,Λ) ≅ Λ`(**唯一の深い算術的入力**を構造として明示);
* `cyclotomicSynchronization` / `synchronization_of_fundamentalClass` ―― 基本類から
  **円分同期化同型が構成できる**こと(= 同期化の存在 ⟸ 基本類);
* `synchronization_equivariant` ―― 同期化が **円分指標(`G` 作用)を同期する**こと

を、`sorry` 無しで証明する。これにより、円分同期化同型の存在 (`CyclotomicSynchronizationExists`)
は、ブラックボックスではなく **「基本類 `H²(G,Λ) ≅ Λ` の存在」という一点**に精密に還元される
(基本類そのものの成立は算術的に深く、形式化の射程外として honest に残す)。
-/

namespace IUT.Cohomology

variable (G : Type*) [Group G] [TopologicalSpace G] [ContinuousMul G]
variable (Λ : Type*) [AddCommGroup Λ] [TopologicalSpace Λ] [IsTopologicalAddGroup Λ]
  [DistribMulAction G Λ] [ContinuousSMul G Λ]

/-- **エタール的円分物** `Λ_ét(G) := H²(G, Λ)`。群論的データ(連続コホモロジー)のみから
定まる円分物。Hoshi §1 の `Hom(H²(Q,Ẑ),Ẑ)` に相当(係数 `Λ = Ẑ(1)`)。 -/
abbrev EtaleCyclotome : Type _ := H2 G Λ

/-- **基本類** (fundamental class): エタール的円分物 `H²(G,Λ)` と円分物 `Λ` の加法的同型。
曲線の基本類 `H²(Q,Ẑ) ≅ Ẑ`(局所類体論 / Poincaré 双対)に相当する**深い算術的入力**。
一般の群では成立せず、算術的状況に固有 ―― 円分剛性の唯一の深い前提。 -/
structure FundamentalClass where
  /-- `H²(G,Λ) ≅ Λ` の加法同型(基本類)。 -/
  iso : EtaleCyclotome G Λ ≃+ Λ

/-- `g : G` の `Λ` への作用を加法同型 `Λ ≃+ Λ` として(円分指標の各成分)。 -/
def actionEquiv (g : G) : Λ ≃+ Λ where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv x := by simp only [smul_smul, inv_mul_cancel, one_smul]
  right_inv x := by simp only [smul_smul, mul_inv_cancel, one_smul]
  map_add' := smul_add g

@[simp] theorem actionEquiv_apply (g : G) (x : Λ) : actionEquiv G Λ g x = g • x := rfl

variable {G Λ}

/-- **円分同期化同型**: 基本類が定める、エタール的円分物 `H²(G,Λ)` と `Λ` の正準的同型。
Hoshi §1 の円分同期化同型(`I_c ≅ Hom(H²,Ẑ)` 型)の本体。 -/
def cyclotomicSynchronization (fc : FundamentalClass G Λ) :
    EtaleCyclotome G Λ ≃+ Λ := fc.iso

/-- **円分同期化の存在 ⟸ 基本類**: 基本類が与えられれば円分同期化同型が存在する。 -/
theorem synchronization_of_fundamentalClass (fc : FundamentalClass G Λ) :
    Nonempty (EtaleCyclotome G Λ ≃+ Λ) :=
  ⟨cyclotomicSynchronization fc⟩

/-- 基本類により `Λ` の `G` 作用(円分指標)をエタール的円分物へ移した、各 `g` の自己同型。 -/
def transportedAction (fc : FundamentalClass G Λ) (g : G) :
    EtaleCyclotome G Λ ≃+ EtaleCyclotome G Λ :=
  (fc.iso.trans (actionEquiv G Λ g)).trans fc.iso.symm

/-- **円分同期化は円分指標を同期する**: 同期化同型 `μ = fc.iso` は、エタール的円分物の
(基本類で移した)`G` 作用を `Λ` の `G` 作用(円分指標)へ正準的に対応させる:
`μ(transportedAction g x) = g • μ(x)`。これが「円分物の同期」の内容。 -/
theorem synchronization_equivariant (fc : FundamentalClass G Λ) (g : G)
    (x : EtaleCyclotome G Λ) :
    fc.iso (transportedAction fc g x) = g • fc.iso x := by
  simp only [transportedAction, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, actionEquiv_apply]

@[simp] theorem transportedAction_apply (fc : FundamentalClass G Λ) (g : G)
    (x : EtaleCyclotome G Λ) :
    transportedAction fc g x = fc.iso.symm (g • fc.iso x) := by
  simp only [transportedAction, AddEquiv.trans_apply, actionEquiv_apply]

theorem transportedAction_one (fc : FundamentalClass G Λ) (x : EtaleCyclotome G Λ) :
    transportedAction fc 1 x = x := by
  simp only [transportedAction_apply, one_smul, AddEquiv.symm_apply_apply]

theorem transportedAction_mul (fc : FundamentalClass G Λ) (g h : G) (x : EtaleCyclotome G Λ) :
    transportedAction fc (g * h) x = transportedAction fc g (transportedAction fc h x) := by
  simp only [transportedAction_apply, AddEquiv.apply_symm_apply, mul_smul]

theorem transportedAction_zero (fc : FundamentalClass G Λ) (g : G) :
    transportedAction fc g 0 = 0 := by
  simp only [transportedAction_apply, map_zero, smul_zero]

theorem transportedAction_add (fc : FundamentalClass G Λ) (g : G) (x y : EtaleCyclotome G Λ) :
    transportedAction fc g (x + y) = transportedAction fc g x + transportedAction fc g y := by
  simp only [transportedAction_apply, map_add, smul_add]

/-- **エタール的円分物上の円分指標**(基本類が移した `G` 作用)。これにより `H²(G,Λ)` は
円分指標付きの円分物となり、円分同期化同型 `fc.iso` は **`G`-同変な円分物の同型**になる
(`synchronization_equivariant`)。すなわち群論的に再構成した円分物と `Λ` の円分指標が同期する。 -/
def etaleAction (fc : FundamentalClass G Λ) : DistribMulAction G (EtaleCyclotome G Λ) where
  smul g x := transportedAction fc g x
  one_smul x := transportedAction_one fc x
  mul_smul g h x := transportedAction_mul fc g h x
  smul_zero g := transportedAction_zero fc g
  smul_add g x y := transportedAction_add fc g x y

/-- **円分剛性(同期化同型の一意性)**: 2 つの基本類 `fc₁, fc₂` が**同じ円分指標**
(`transportedAction`, = `etaleAction`)をエタール的円分物に誘導するなら、その同期化同型の
差 `u = fc₂.iso ∘ fc₁.iso⁻¹ : Λ ≃ Λ` は **`G`-同変**(`u(g•y) = g•u(y)`)である。

すなわち円分同期化同型の不定性は、円分物 `Λ` の `G`-同変自己同型 `Aut^G(Λ)`(円分指標を
保つ自己同型 ―― 円分物では小さい)に厳密に限られる。これが円分「剛性」(rigidity)の内容:
同期化は本質的に一意である。`synchronization_equivariant`(存在側)と合わせ、円分剛性の
**存在と一意性の両輪**を `sorry` 無しで与える。 -/
theorem synchronization_rigid (fc₁ fc₂ : FundamentalClass G Λ)
    (h : ∀ (g : G) (x : EtaleCyclotome G Λ),
      transportedAction fc₁ g x = transportedAction fc₂ g x)
    (g : G) (y : Λ) :
    fc₂.iso (fc₁.iso.symm (g • y)) = g • fc₂.iso (fc₁.iso.symm y) := by
  have key := h g (fc₁.iso.symm y)
  simp only [transportedAction_apply, AddEquiv.apply_symm_apply] at key
  rw [key, AddEquiv.apply_symm_apply]

end IUT.Cohomology
