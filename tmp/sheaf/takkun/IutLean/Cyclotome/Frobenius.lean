import Mathlib

/-!
# Frobenius 的円分物 `Λ(M) = lim_n μ_n(M)`(Tate 加群 `Ẑ(1)`)

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§2 / [FrdI], [AbsTopII] Prop 3.2 等。

円分剛性(cyclotomic rigidity)は IUT を貫く技術的道具であり(§1 群論版・§2 局所類体論版・
§15 単テータ版のすべてに現れる)、その核は**円分物** `Λ`(Tate 捻り `Ẑ(1)`)である。

フロベニオイド `G ↷ M`(`M ≅ O▷_k` などのモノイド)から得られる **Frobenius 的円分物**は
`Λ(M) = lim_n M[n] = lim_n μ_n(M)`
であり、各 `μ_n(M)`(`n` 乗根のなす群、Mathlib `rootsOfUnity n M`)を遷移写像
`ζ ↦ ζ^m : μ_{nm}(M) → μ_n(M)` で繋いだ**逆極限**である。

本ファイルでは、この逆極限を「両立的な根の族」のなす群として `sorry` 無しに構築する。
これが Frobenius 的円分物 `Λ(M)`(Ẑ(1) の Frobenius 的実現)であり、円分剛性理論の出発点。
-/

namespace IUT.Cyclotome

variable (M : Type*) [CommMonoid M]

/-- **遷移写像** `μ_{n·m}(M) → μ_n(M)`, `ζ ↦ ζ^m`。
(`ζ^(nm) = 1` ならば `(ζ^m)^n = ζ^(nm) = 1` ゆえ `ζ^m ∈ μ_n`。) -/
def rouTransition (n m : ℕ) : rootsOfUnity (n * m) M →* rootsOfUnity n M where
  toFun ζ := ⟨(ζ : Mˣ) ^ m, by
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm m n]
    exact (mem_rootsOfUnity _ _).mp ζ.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_pow]

@[simp] theorem rouTransition_coe (n m : ℕ) (ζ : rootsOfUnity (n * m) M) :
    ((rouTransition M n m ζ : Mˣ)) = (ζ : Mˣ) ^ m := rfl

/-- **Frobenius 的円分物** `Λ(M) = lim_n μ_n(M)`: 各 `n` の `n` 乗根 `ζ_n` であって、
遷移写像と両立する(`(ζ_{n·m})^m = ζ_n`、ただし `m ≠ 0`)族のなす群。
Tate 捻り `Ẑ(1)` の Frobenius 的実現。

**`m ≠ 0` ガードが本質的(2026-07-06 修正)**: `m = 0` まで両立性を要求すると
遷移写像 `ζ ↦ ζ⁰ = 1` が全成分 `f n = 1` を強制し `Λ(M)` が**自明群に退化**する
(恒真 proxy 禁止の鉄則に反する空虚化)。ガード付きの本定義は `n ≥ 1` 上の真の逆極限であり、
非自明性は `Cyclotome/Kummer.lean` の `frobeniusCyclotome_nontrivial`(`ℂ` 上の明示的
witness `exp(2πi/n)`)で検証済。 -/
def FrobeniusCyclotome : Subgroup (∀ n : ℕ, rootsOfUnity n M) where
  carrier := {f | ∀ n m : ℕ, m ≠ 0 → rouTransition M n m (f (n * m)) = f n}
  one_mem' := by intro n m _; simp
  mul_mem' {f g} hf hg := by
    intro n m hm
    simp only [Pi.mul_apply, map_mul, hf n m hm, hg n m hm]
  inv_mem' {f} hf := by
    intro n m hm
    simp only [Pi.inv_apply, map_inv, hf n m hm]

/-- `Λ(M)` は可換群。 -/
noncomputable instance : CommGroup (FrobeniusCyclotome M) := inferInstance

/-- `Λ(M)` の元の第 `n` 成分(`n` 乗根)。 -/
def component (f : FrobeniusCyclotome M) (n : ℕ) : rootsOfUnity n M := f.1 n

/-- 両立性(円分物の定義条件): `(ζ_{n·m})^m = ζ_n`(`m ≠ 0`)。 -/
theorem component_compat (f : FrobeniusCyclotome M) (n m : ℕ) (hm : m ≠ 0) :
    rouTransition M n m (component M f (n * m)) = component M f n :=
  f.2 n m hm

/-! ## 関手性: `Λ` はモノイド準同型に沿って関手的 -/

variable {N : Type*} [CommMonoid N]

/-- モノイド準同型 `φ : M → N` が誘導する `μ_n(M) → μ_n(N)`(`ζ ↦ φ(ζ)`)。 -/
def rouMap (φ : M →* N) (k : ℕ) : rootsOfUnity k M →* rootsOfUnity k N where
  toFun ζ := ⟨Units.map φ ζ, by
    rw [mem_rootsOfUnity, ← map_pow, (mem_rootsOfUnity _ _).mp ζ.2, map_one]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp

@[simp] theorem rouMap_coe (φ : M →* N) (k : ℕ) (ζ : rootsOfUnity k M) :
    ((rouMap M φ k ζ : Nˣ)) = Units.map φ (ζ : Mˣ) := rfl

/-- **自然性**: 関手性写像 `rouMap` は遷移写像 `rouTransition` と可換
(`φ(ζ^m) = φ(ζ)^m` ゆえ)。 -/
theorem rouTransition_rouMap (φ : M →* N) (n m : ℕ) (ζ : rootsOfUnity (n * m) M) :
    rouTransition N n m (rouMap M φ (n * m) ζ) = rouMap M φ n (rouTransition M n m ζ) := by
  apply Subtype.ext
  simp [map_pow]

/-- **`Λ` の関手性**: モノイド準同型 `φ : M → N` は群準同型 `Λ(φ) : Λ(M) → Λ(N)` を誘導する。
これにより円分物 `Λ` は関手であり、円分剛性同型が関手的に振る舞う基盤となる(Hoshi §2)。 -/
def map (φ : M →* N) : FrobeniusCyclotome M →* FrobeniusCyclotome N where
  toFun f := ⟨fun n => rouMap M φ n (f.1 n), by
    intro n m hm
    rw [rouTransition_rouMap, f.2 n m hm]⟩
  map_one' := by apply Subtype.ext; ext n; simp
  map_mul' a b := by apply Subtype.ext; ext n; simp

/-! ## 逆極限の普遍性: `Λ(M)` は遷移系 `μ_n` の逆極限 -/

/-- 第 `n` 成分への**射影** `Λ(M) →* μ_n(M)`。 -/
def proj (n : ℕ) : FrobeniusCyclotome M →* rootsOfUnity n M where
  toFun f := f.1 n
  map_one' := rfl
  map_mul' _ _ := rfl

/-- 射影は遷移写像と両立する: `rouTransition ∘ proj_{n·m} = proj_n`(逆極限の錐条件、`m ≠ 0`)。 -/
theorem rouTransition_proj (n m : ℕ) (hm : m ≠ 0) (f : FrobeniusCyclotome M) :
    rouTransition M n m (proj M (n * m) f) = proj M n f :=
  f.2 n m hm

/-- **逆極限の普遍性**: 群 `K` から各 `μ_n(M)` への、遷移写像と両立する射の族 `g` が与えられると、
それらを一意に束ねる射 `K →* Λ(M)` が得られる。これにより `Λ(M)` が遷移系 `{μ_n}` の逆極限
であることが特徴付けられる ―― 円分剛性同型(`Λ(M) ≅ Λ(G)`)を構成する際の普遍的道具。 -/
def lift {K : Type*} [CommGroup K] (g : ∀ n : ℕ, K →* rootsOfUnity n M)
    (hg : ∀ n m : ℕ, m ≠ 0 → (rouTransition M n m).comp (g (n * m)) = g n) :
    K →* FrobeniusCyclotome M where
  toFun x := ⟨fun n => g n x, fun n m hm => by
    have h := DFunLike.congr_fun (hg n m hm) x
    rwa [MonoidHom.comp_apply] at h⟩
  map_one' := by apply Subtype.ext; ext n; simp
  map_mul' a b := by apply Subtype.ext; ext n; simp

/-- 普遍性の射 `lift` は射影で元の族 `g` を復元する: `proj_n ∘ lift g = g n`。 -/
@[simp] theorem proj_lift {K : Type*} [CommGroup K] (g : ∀ n : ℕ, K →* rootsOfUnity n M)
    (hg : ∀ n m : ℕ, m ≠ 0 → (rouTransition M n m).comp (g (n * m)) = g n) (n : ℕ) :
    (proj M n).comp (lift M g hg) = g n := rfl

/-- **逆極限の一意性(= 円分剛性の核心)**: `Λ(M)` への 2 つの射が、すべての射影 `proj_n` で一致すれば
等しい。これにより円分物への射 ―― 特に**円分剛性同型** ―― は射影によって**一意に**決まる。
すなわち「正準的同型の一意性」であり、円分剛性が剛性(rigidity)である所以。 -/
theorem hom_ext {K : Type*} [CommGroup K] {h₁ h₂ : K →* FrobeniusCyclotome M}
    (heq : ∀ n, (proj M n).comp h₁ = (proj M n).comp h₂) : h₁ = h₂ := by
  apply MonoidHom.ext; intro x
  apply Subtype.ext; funext n
  exact DFunLike.congr_fun (heq n) x

/-! ## `Λ` の関手則: `Λ` は(乗法モノイドの圏からの)関手 -/

variable {L : Type*} [CommMonoid L]

theorem rouMap_id (k : ℕ) : rouMap M (MonoidHom.id M) k = MonoidHom.id _ := by
  ext ζ; simp

theorem rouMap_comp (φ : M →* N) (ψ : L →* M) (k : ℕ) :
    rouMap L (φ.comp ψ) k = (rouMap M φ k).comp (rouMap L ψ k) := by
  ext ζ; simp

/-- **関手則(恒等)**: `Λ(id) = id`。 -/
@[simp] theorem map_id : map M (MonoidHom.id M) = MonoidHom.id (FrobeniusCyclotome M) := by
  apply MonoidHom.ext; intro f
  apply Subtype.ext; funext n
  show rouMap M (MonoidHom.id M) n (f.1 n) = f.1 n
  rw [rouMap_id, MonoidHom.id_apply]

/-- **関手則(合成)**: `Λ(φ ∘ ψ) = Λ(φ) ∘ Λ(ψ)`。 -/
theorem map_comp (φ : M →* N) (ψ : L →* M) :
    map L (φ.comp ψ) = (map M φ).comp (map L ψ) := by
  apply MonoidHom.ext; intro f
  apply Subtype.ext; funext n
  show rouMap L (φ.comp ψ) n (f.1 n) = rouMap M φ n (rouMap L ψ n (f.1 n))
  rw [rouMap_comp]; rfl

/-! ## 円分指標: 自己同型による `Λ(K)` への作用(= `Ẑ(1)` の Galois 作用) -/

/-- 乗法自己同型 `σ : K ≃* K` が円分物 `Λ(K)` に誘導する**自己同型**(関手則 `Λ(σ∘σ⁻¹)=id` による)。
体の Galois 自己同型に対してこれは **円分指標** ―― エタール的円分物 `Ẑ(1)` への Galois 作用 ―― となる。 -/
def cyclotomicAut (σ : M ≃* M) : FrobeniusCyclotome M ≃* FrobeniusCyclotome M where
  toFun := map M σ.toMonoidHom
  invFun := map M σ.symm.toMonoidHom
  left_inv f := by
    have hid : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id M := by ext x; simp
    show ((map M σ.symm.toMonoidHom).comp (map M σ.toMonoidHom)) f = f
    rw [← map_comp, hid, map_id]; rfl
  right_inv f := by
    have hid : σ.toMonoidHom.comp σ.symm.toMonoidHom = MonoidHom.id M := by ext x; simp
    show ((map M σ.toMonoidHom).comp (map M σ.symm.toMonoidHom)) f = f
    rw [← map_comp, hid, map_id]; rfl
  map_mul' a b := (map M σ.toMonoidHom).map_mul a b

/-- **円分指標の群作用性**: `σ ↦ Λ(σ)` は乗法自己同型群 `K ≃* K` から `Λ(K)` の自己同型群への
群準同型(関手則 `Λ(id)=id`, `Λ(σ∘τ)=Λ(σ)∘Λ(τ)` による)。これが `Ẑ(1)` の正準的 Galois 作用。 -/
def cyclotomicChar : (M ≃* M) →* MulAut (FrobeniusCyclotome M) where
  toFun := cyclotomicAut M
  map_one' := by
    apply DFunLike.ext; intro f
    have h1 : (1 : M ≃* M).toMonoidHom = MonoidHom.id M := by ext x; rfl
    show map M (1 : M ≃* M).toMonoidHom f = f
    rw [h1, map_id]; rfl
  map_mul' σ τ := by
    apply DFunLike.ext; intro f
    have hcomp : (σ * τ).toMonoidHom = σ.toMonoidHom.comp τ.toMonoidHom := by ext x; rfl
    show map M (σ * τ).toMonoidHom f = map M σ.toMonoidHom (map M τ.toMonoidHom f)
    rw [hcomp, map_comp]; rfl

/-- **円分指標の成分ごとの記述**: 自己同型 `σ` は各レベルの根 `ζ_n ∈ μ_n(M)` に、
体の自己同型 `σ` をそのまま適用して作用する(`proj_n(σ·f) = σ(proj_n f)`)。
これが「`Ẑ(1)` への Galois 作用が、各 `μ_n` 上の自然な作用の逆極限である」ことの具体的内容。 -/
@[simp] theorem proj_cyclotomicAut (σ : M ≃* M) (n : ℕ) (f : FrobeniusCyclotome M) :
    proj M n (cyclotomicAut M σ f) = rouMap M σ.toMonoidHom n (proj M n f) := rfl

/-- 円分指標は単数 `ζ_n` の像を体の自己同型で与える: `(σ·f) の n 成分の値 = σ(f の n 成分の値)`。 -/
theorem cyclotomicAut_component_coe (σ : M ≃* M) (n : ℕ) (f : FrobeniusCyclotome M) :
    ((proj M n (cyclotomicAut M σ f) : Mˣ)) = Units.map σ.toMonoidHom (proj M n f : Mˣ) := rfl

/-- 射影の関手性: `proj_n ∘ Λ(φ) = μ_n(φ) ∘ proj_n`。 -/
@[simp] theorem proj_map {N : Type*} [CommMonoid N] (φ : M →* N) (n : ℕ)
    (f : FrobeniusCyclotome M) : proj N n (map M φ f) = rouMap M φ n (proj M n f) := rfl

/-- **円分指標の自然性(= 円分剛性が正準的である本質)**: モノイド準同型 `φ : M → N` が自己同型
`σ`(`M` 上)と `τ`(`N` 上)を絡める(`φ∘σ = τ∘φ`)とき、`Λ(φ)` は円分指標と可換:
`Λ(φ) ∘ (σ への作用) = (τ への作用) ∘ Λ(φ)`。これが「円分指標 = `Ẑ(1)` の Galois 作用」が
関手的・正準的であること ―― 円分剛性が剛性たる所以の核心。 -/
theorem cyclotomicChar_naturality {N : Type*} [CommMonoid N] (φ : M →* N)
    (σ : M ≃* M) (τ : N ≃* N) (h : φ.comp σ.toMonoidHom = τ.toMonoidHom.comp φ) :
    (map M φ).comp (cyclotomicAut M σ).toMonoidHom
      = (cyclotomicAut N τ).toMonoidHom.comp (map M φ) := by
  refine hom_ext (M := N) ?_
  intro n
  apply MonoidHom.ext; intro f
  have hL : rouMap M φ n (rouMap M σ.toMonoidHom n (proj M n f))
          = rouMap M (φ.comp σ.toMonoidHom) n (proj M n f) := by rw [rouMap_comp]; rfl
  have hR : rouMap N τ.toMonoidHom n (rouMap M φ n (proj M n f))
          = rouMap M (τ.toMonoidHom.comp φ) n (proj M n f) := by rw [rouMap_comp]; rfl
  show rouMap M φ n (rouMap M σ.toMonoidHom n (proj M n f))
     = rouMap N τ.toMonoidHom n (rouMap M φ n (proj M n f))
  rw [hL, hR, h]

end IUT.Cyclotome
