import Mathlib

/-!
# 連続群コホモロジー(低次)― Continuous group cohomology in low degrees

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§1, §2 / Mochizuki [AbsTopIII], [FrdI]。

IUT の円分剛性(円分同期化同型 `CyclotomicSynchronizationExists`)は、エタール的円分物
`Λ(G) = Hom(H²(G,Ẑ), Ẑ)` と局所類体論由来の円分物 `Λ(M)` を結ぶ。その基盤となる
**連続(プロ有限)群コホモロジー** ―― 位相群 `G` が位相加群 `M` に**連続**作用するときの
連続コチェイン複体 ―― は Mathlib に未整備である(Mathlib の `groupCohomology` は
**離散群・`k`-加群**上の不均質コチェインで、位相・連続性・`Ẑ` 係数を扱わない)。

本モジュールでは、その第一層として **低次(`H⁰`, `H¹`)の連続群コホモロジー** を一から構築する:

* `cochain 0/1/2` ―― 連続コチェイン `M`, `C(G,M)`, `C(G×G,M)`(`ContinuousMap` で連続性を内蔵);
* 余境界作用素 `d0 : M →+ C(G,M)`, `d1 : C(G,M) →+ C(G×G,M)`(連続性込みで構成);
* **`d1_comp_d0` ― コチェイン複体の条件 `d¹∘d⁰ = 0`**;
* `H0 = M^G`(連続不変元 = `ker d0`)とその特徴付け `mem_H0`;
* `oneCocycles = ker d1`(連続 1-余輪体 / crossed hom)、`oneCoboundaries = range d0`、
  包含 `oneCoboundaries ≤ oneCocycles`、そして **`H1`(第 1 連続コホモロジー)**。

`G` の位相群性は `[ContinuousMul G]`(余境界の式に逆元は現れない)、`M` の位相加群性は
`[IsTopologicalAddGroup M]`、作用の連続性は `[ContinuousSMul G M]` で表す。すべて標準公理のみ。
-/

namespace IUT.Cohomology

open ContinuousMap

variable (G : Type*) [Group G] [TopologicalSpace G] [ContinuousMul G]
variable (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
variable [DistribMulAction G M] [ContinuousSMul G M]

/-! ## 連続コチェイン -/

/-- 連続 0-コチェイン `C⁰(G,M) = M`(定数)。 -/
abbrev Cochain0 : Type _ := M

/-- 連続 1-コチェイン `C¹(G,M) = C(G,M)`(連続写像 `G → M`)。 -/
abbrev Cochain1 : Type _ := C(G, M)

/-- 連続 2-コチェイン `C²(G,M) = C(G×G,M)`。 -/
abbrev Cochain2 : Type _ := C(G × G, M)

/-! ## 余境界作用素 -/

/-- **0 次余境界** `d⁰ : M → C(G,M)`、`(d⁰ m)(g) = g•m - m`。連続性は作用の連続性から。 -/
def d0 : M →+ C(G, M) where
  toFun m := ⟨fun g => g • m - m, (continuous_id.smul continuous_const).sub continuous_const⟩
  map_zero' := by ext g; simp
  map_add' m m' := by ext g; simp [smul_add]; abel

/-- **1 次余境界** `d¹ : C(G,M) → C(G×G,M)`、`(d¹ f)(g,h) = g•f(h) - f(g·h) + f(g)`。 -/
def d1 : C(G, M) →+ C(G × G, M) where
  toFun f := ⟨fun p => p.1 • f p.2 - f (p.1 * p.2) + f p.1,
    ((continuous_fst.smul (f.continuous.comp continuous_snd)).sub
        (f.continuous.comp continuous_mul)).add (f.continuous.comp continuous_fst)⟩
  map_zero' := by ext p; simp
  map_add' f f' := by
    ext p
    simp only [coe_mk, ContinuousMap.add_apply, smul_add]
    abel

@[simp] theorem d0_apply (m : M) (g : G) : d0 G M m g = g • m - m := rfl

@[simp] theorem d1_apply (f : C(G, M)) (g h : G) :
    d1 G M f (g, h) = g • f h - f (g * h) + f g := rfl

/-! ## コチェイン複体の条件 `d¹ ∘ d⁰ = 0` -/

/-- **連続コチェイン複体**: `d¹ ∘ d⁰ = 0`。`(d¹(d⁰ m))(g,h) = g•(h•m - m) - ((gh)•m - m) + (g•m - m)`
が `g•(h•m) = (g·h)•m`(`mul_smul`)で相殺して `0` になる。 -/
theorem d1_comp_d0 (m : M) : d1 G M (d0 G M m) = 0 := by
  ext p
  obtain ⟨g, h⟩ := p
  simp only [d1_apply, d0_apply, ContinuousMap.zero_apply, smul_sub, mul_smul]
  abel

/-! ## `H⁰` ― 連続不変元 -/

/-- **第 0 連続コホモロジー** `H⁰(G,M) = M^G`(連続不変元 = `ker d⁰`)。 -/
def H0 : AddSubgroup M := (d0 G M).ker

/-- `H⁰` の特徴付け: `m ∈ H⁰ ⟺ ∀ g, g•m = m`(`G`-不変)。 -/
theorem mem_H0 {m : M} : m ∈ H0 G M ↔ ∀ g : G, g • m = m := by
  rw [H0, AddMonoidHom.mem_ker, ContinuousMap.ext_iff]
  simp [sub_eq_zero]

/-! ## `H¹` ― 第 1 連続コホモロジー -/

/-- **連続 1-余輪体** `Z¹(G,M) = ker d¹`(連続 crossed homomorphism)。 -/
def oneCocycles : AddSubgroup C(G, M) := (d1 G M).ker

/-- **連続 1-余境界** `B¹(G,M) = range d⁰`。 -/
def oneCoboundaries : AddSubgroup C(G, M) := (d0 G M).range

/-- 余境界は余輪体(`B¹ ≤ Z¹`)。コチェイン複体 `d¹∘d⁰ = 0` の直接の帰結。 -/
theorem oneCoboundaries_le_oneCocycles : oneCoboundaries G M ≤ oneCocycles G M := by
  rintro _ ⟨m, rfl⟩
  rw [oneCocycles, AddMonoidHom.mem_ker]
  exact d1_comp_d0 G M m

/-- **第 1 連続コホモロジー** `H¹(G,M) = Z¹ / B¹`。連続 crossed homomorphism を連続主等質
(coboundary)で割ったもの。円分指標・ねじれ Tate 加群の分類に現れる。 -/
abbrev H1 : Type _ :=
  oneCocycles G M ⧸ (oneCoboundaries G M).addSubgroupOf (oneCocycles G M)

/-- 連続 1-余輪体の特徴付け: `f ∈ Z¹ ⟺ ∀ g h, f(g·h) = g•f(h) + f(g)`(crossed hom 条件)。 -/
theorem mem_oneCocycles {f : C(G, M)} :
    f ∈ oneCocycles G M ↔ ∀ g h : G, f (g * h) = g • f h + f g := by
  rw [oneCocycles, AddMonoidHom.mem_ker, ContinuousMap.ext_iff]
  constructor
  · intro hf g h
    have h0 : g • f h - f (g * h) + f g = 0 := by
      have := hf (g, h); rwa [d1_apply, ContinuousMap.zero_apply] at this
    have hsub : (g • f h + f g) - f (g * h) = 0 := by rw [← h0]; abel
    exact (sub_eq_zero.mp hsub).symm
  · rintro hf ⟨g, h⟩
    rw [d1_apply, ContinuousMap.zero_apply, hf g h]
    abel

/-! ## `H²` ― 第 2 連続コホモロジー(中心拡大の分類)

`H²(G,M)` は **中心拡大 `1 → M → E → G → 1`** の同値類を分類する(`M` は中心)。IUT では
これが **円分物 `Λ = Ẑ(1)` を中心とするテータ群**(`IUT.Theta.IsThetaGroup`、中心拡大
`1→Λ→Gθ→Π→1`)の座席であり、曲線の**基本類** `H²(Q,Ẑ) ≅ Ẑ` ―― 円分同期化同型
`CyclotomicSynchronizationExists` の核 ―― が住む場所である。 -/

/-- 連続 3-コチェイン `C³(G,M) = C(G×G×G, M)`。 -/
abbrev Cochain3 : Type _ := C(G × G × G, M)

/-- **2 次余境界** `d² : C(G×G,M) → C(G×G×G,M)`、
`(d² c)(g,h,k) = g•c(h,k) - c(g·h,k) + c(g,h·k) - c(g,h)`。これが `0` であることが
**2-余輪体条件(因子団 / factor system)** = 中心拡大の結合律。 -/
def d2 : C(G × G, M) →+ C(G × G × G, M) where
  toFun c := ⟨fun p => p.1 • c (p.2.1, p.2.2) - c (p.1 * p.2.1, p.2.2)
      + c (p.1, p.2.1 * p.2.2) - c (p.1, p.2.1), by fun_prop⟩
  map_zero' := by ext p; simp
  map_add' c c' := by ext p; simp only [coe_mk, ContinuousMap.add_apply, smul_add]; abel

@[simp] theorem d2_apply (c : C(G × G, M)) (g h k : G) :
    d2 G M c (g, h, k) = g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) := rfl

/-- **連続コチェイン複体(2 段目)**: `d² ∘ d¹ = 0`。`g•(h•f k) = (g·h)•f k`(`mul_smul`)と
`(g·h)·k = g·(h·k)`(`mul_assoc`)で全項が相殺する。 -/
theorem d2_comp_d1 (f : C(G, M)) : d2 G M (d1 G M f) = 0 := by
  ext p
  obtain ⟨g, h, k⟩ := p
  simp only [d2_apply, d1_apply, ContinuousMap.zero_apply, smul_sub, smul_add, mul_smul, mul_assoc]
  abel

/-- **連続 2-余輪体** `Z²(G,M) = ker d²`(因子団 / 中心拡大の因子系)。 -/
def twoCocycles : AddSubgroup C(G × G, M) := (d2 G M).ker

/-- **連続 2-余境界** `B²(G,M) = range d¹`。 -/
def twoCoboundaries : AddSubgroup C(G × G, M) := (d1 G M).range

/-- 余境界は余輪体(`B² ≤ Z²`)。`d²∘d¹ = 0` の帰結。 -/
theorem twoCoboundaries_le_twoCocycles : twoCoboundaries G M ≤ twoCocycles G M := by
  rintro _ ⟨f, rfl⟩
  rw [twoCocycles, AddMonoidHom.mem_ker]
  exact d2_comp_d1 G M f

/-- **第 2 連続コホモロジー** `H²(G,M) = Z² / B²`。中心拡大 `1→M→E→G→1` の同値類を分類する。 -/
abbrev H2 : Type _ :=
  twoCocycles G M ⧸ (twoCoboundaries G M).addSubgroupOf (twoCocycles G M)

/-- 連続 2-余輪体の特徴付け = **因子団の結合律**:
`f ∈ Z² ⟺ ∀ g h k, g•c(h,k) + c(g,h·k) = c(g·h,k) + c(g,h)`。
これは中心拡大 `1→M→E→G→1` における因子系の整合条件そのもの。 -/
theorem mem_twoCocycles {c : C(G × G, M)} :
    c ∈ twoCocycles G M ↔
      ∀ g h k : G, g • c (h, k) + c (g, h * k) = c (g * h, k) + c (g, h) := by
  rw [twoCocycles, AddMonoidHom.mem_ker, ContinuousMap.ext_iff]
  constructor
  · intro hc g h k
    have h0 : g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
      have := hc (g, h, k); rwa [d2_apply, ContinuousMap.zero_apply] at this
    have hsub : (g • c (h, k) + c (g, h * k)) - (c (g * h, k) + c (g, h)) = 0 := by
      rw [← h0]; abel
    exact sub_eq_zero.mp hsub
  · rintro hc ⟨g, h, k⟩
    rw [d2_apply, ContinuousMap.zero_apply]
    have h2 := sub_eq_zero.mpr (hc g h k)
    rw [← h2]; abel

/-! ## 係数関手性 ― 連続 `G`-同変写像が誘導するコホモロジー写像

係数の連続加群写像 `ψ : M →+ N` が `G`-同変(`ψ(g•m) = g•ψ(m)`)かつ連続なら、各次の
連続コチェインに後合成として作用し、余境界 `d` と可換になる。よって**連続コチェイン複体の射**を
与え、`H⁰`/`H¹`/`H²` の間の誘導準同型を得る。円分物の比較 `Λ(M)≅Λ(G)` 等、係数を取り替える
正準的同型の基盤。 -/

section Functoriality

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]
  (ψ : M →+ N) (hψ : Continuous ψ) (hψe : ∀ (g : G) (m : M), ψ (g • m) = g • ψ m)

/-- 係数写像 `ψ` が誘導する 1-コチェイン写像 `C(G,M) → C(G,N)`(`ψ` で後合成)。 -/
def mapC1 : C(G, M) →+ C(G, N) where
  toFun f := ⟨fun g => ψ (f g), hψ.comp f.continuous⟩
  map_zero' := by ext g; simp
  map_add' f f' := by ext g; simp

@[simp] theorem mapC1_apply (f : C(G, M)) (g : G) : mapC1 G M ψ hψ f g = ψ (f g) := rfl

/-- 係数写像 `ψ` が誘導する 2-コチェイン写像 `C(G×G,M) → C(G×G,N)`。 -/
def mapC2 : C(G × G, M) →+ C(G × G, N) where
  toFun c := ⟨fun p => ψ (c p), hψ.comp c.continuous⟩
  map_zero' := by ext p; simp
  map_add' c c' := by ext p; simp

@[simp] theorem mapC2_apply (c : C(G × G, M)) (p : G × G) : mapC2 G M ψ hψ c p = ψ (c p) := rfl

include hψe

/-- 後合成は `d⁰` と可換: `ψ ∘ d⁰(m) = d⁰(ψ m)`(`ψ` の加法性・同変性による)。 -/
theorem mapC1_comp_d0 (m : M) : mapC1 G M ψ hψ (d0 G M m) = d0 G N (ψ m) := by
  ext g; simp only [mapC1_apply, d0_apply, map_sub, hψe]

/-- 後合成は `d¹` と可換: `ψ ∘ d¹(f) = d¹(ψ ∘ f)`(コチェイン複体の射である条件)。 -/
theorem mapC2_comp_d1 (f : C(G, M)) :
    mapC2 G M ψ hψ (d1 G M f) = d1 G N (mapC1 G M ψ hψ f) := by
  ext p; obtain ⟨g, h⟩ := p
  simp only [mapC2_apply, d1_apply, mapC1_apply, map_add, map_sub, hψe]

/-- 後合成は 1-余輪体を保つ。 -/
theorem mapC1_mem_oneCocycles {f : C(G, M)} (hf : f ∈ oneCocycles G M) :
    mapC1 G M ψ hψ f ∈ oneCocycles G N := by
  rw [mem_oneCocycles] at hf ⊢
  intro g h
  simp only [mapC1_apply]
  have h1 := congrArg ψ (hf g h)
  rw [map_add, hψe] at h1
  exact h1

/-- 後合成は 2-余輪体を保つ。 -/
theorem mapC2_mem_twoCocycles {c : C(G × G, M)} (hc : c ∈ twoCocycles G M) :
    mapC2 G M ψ hψ c ∈ twoCocycles G N := by
  rw [mem_twoCocycles] at hc ⊢
  intro g h k
  simp only [mapC2_apply]
  have h1 := congrArg ψ (hc g h k)
  rw [map_add, map_add, hψe] at h1
  exact h1

/-- **`H⁰` の誘導写像** `H⁰(G,M) → H⁰(G,N)`(連続不変元の像は連続不変元)。 -/
def mapH0 : H0 G M →+ H0 G N :=
  (ψ.comp (H0 G M).subtype).codRestrict (H0 G N) fun x => by
    rw [mem_H0]; intro g
    show g • ψ (x : M) = ψ (x : M)
    rw [← hψe]
    exact congrArg ψ ((mem_H0 G M).mp x.2 g)

/-- 1-余輪体への制限写像 `Z¹(G,M) → Z¹(G,N)`。 -/
def mapZ1 : oneCocycles G M →+ oneCocycles G N :=
  ((mapC1 G M ψ hψ).comp (oneCocycles G M).subtype).codRestrict (oneCocycles G N)
    fun x => mapC1_mem_oneCocycles G M ψ hψ hψe x.2

/-- **`H¹` の誘導写像** `H¹(G,M) → H¹(G,N)`。余輪体を余輪体に、余境界を余境界に送ることから降下。 -/
def mapH1 : H1 G M →+ H1 G N :=
  QuotientAddGroup.map _ _ (mapZ1 G M ψ hψ hψe) (by
    rintro x hx
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp hx)
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact AddMonoidHom.mem_range.mpr ⟨ψ m, by
      show d0 G N (ψ m) = mapC1 G M ψ hψ (x : C(G, M))
      rw [← mapC1_comp_d0 G M ψ hψ hψe m, hm]⟩)

/-- 2-余輪体への制限写像 `Z²(G,M) → Z²(G,N)`。 -/
def mapZ2 : twoCocycles G M →+ twoCocycles G N :=
  ((mapC2 G M ψ hψ).comp (twoCocycles G M).subtype).codRestrict (twoCocycles G N)
    fun x => mapC2_mem_twoCocycles G M ψ hψ hψe x.2

/-- **`H²` の誘導写像** `H²(G,M) → H²(G,N)`。中心拡大の係数取り替えに対応。 -/
def mapH2 : H2 G M →+ H2 G N :=
  QuotientAddGroup.map _ _ (mapZ2 G M ψ hψ hψe) (by
    rintro x hx
    obtain ⟨f, hf⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp hx)
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact AddMonoidHom.mem_range.mpr ⟨mapC1 G M ψ hψ f, by
      show d1 G N (mapC1 G M ψ hψ f) = mapC2 G M ψ hψ (x : C(G × G, M))
      rw [← mapC2_comp_d1 G M ψ hψ hψe f, hf]⟩)

end Functoriality

/-! ## 群変数の関手性 ― 連続群準同型による引き戻し(restriction / inflation)

連続群準同型 `φ : G' →* G` に沿って、`G`-加群 `M` を `G'`-加群とみなす(`g'•m := φ(g')•m`、
互換性 `hφc`)。すると各次の連続コチェインに**前合成**として作用し、余境界 `d` と可換になる。
`φ` が部分群の包含なら **restriction**、商への射影なら **inflation** であり、両者を統一する。
inflation-restriction 完全列、ひいては円分物 `Λ(G)` の群論的記述の基盤。 -/

section Restriction

variable {G' : Type*} [Group G'] [TopologicalSpace G'] [ContinuousMul G']
  [DistribMulAction G' M] [ContinuousSMul G' M]
  (φ : G' →* G) (hφ : Continuous φ) (hφc : ∀ (g' : G') (m : M), φ g' • m = g' • m)

/-- 連続群準同型 `φ` に沿う 1-コチェインの引き戻し `C(G,M) → C(G',M)`(`φ` で前合成)。 -/
def pullC1 : C(G, M) →+ C(G', M) where
  toFun f := ⟨fun g' => f (φ g'), f.continuous.comp hφ⟩
  map_zero' := by ext g'; simp
  map_add' f f' := by ext g'; simp

@[simp] theorem pullC1_apply (f : C(G, M)) (g' : G') : pullC1 G M φ hφ f g' = f (φ g') := rfl

/-- `φ` に沿う 2-コチェインの引き戻し `C(G×G,M) → C(G'×G',M)`。 -/
def pullC2 : C(G × G, M) →+ C(G' × G', M) where
  toFun c := ⟨fun p => c (φ p.1, φ p.2),
    c.continuous.comp ((hφ.comp continuous_fst).prodMk (hφ.comp continuous_snd))⟩
  map_zero' := by ext p; simp
  map_add' c c' := by ext p; simp

@[simp] theorem pullC2_apply (c : C(G × G, M)) (g' h' : G') :
    pullC2 G M φ hφ c (g', h') = c (φ g', φ h') := rfl

include hφc

/-- 引き戻しは `d⁰` と可換: `(d⁰_G m) ∘ φ = d⁰_{G'} m`(作用の互換性 `hφc` による)。 -/
theorem pullC1_comp_d0 (m : M) : pullC1 G M φ hφ (d0 G M m) = d0 G' M m := by
  ext g'; simp only [pullC1_apply, d0_apply, hφc]

/-- 引き戻しは `d¹` と可換: 引き戻しは連続コチェイン複体の射。 -/
theorem pullC2_comp_d1 (f : C(G, M)) :
    pullC2 G M φ hφ (d1 G M f) = d1 G' M (pullC1 G M φ hφ f) := by
  ext p; obtain ⟨g', h'⟩ := p
  simp only [pullC2_apply, d1_apply, pullC1_apply, map_mul, hφc]

/-- 引き戻しは 1-余輪体を保つ。 -/
theorem pullC1_mem_oneCocycles {f : C(G, M)} (hf : f ∈ oneCocycles G M) :
    pullC1 G M φ hφ f ∈ oneCocycles G' M := by
  rw [mem_oneCocycles] at hf ⊢
  intro g' h'
  simp only [pullC1_apply]
  rw [map_mul, hf (φ g') (φ h'), hφc]

/-- 引き戻しは 2-余輪体を保つ。 -/
theorem pullC2_mem_twoCocycles {c : C(G × G, M)} (hc : c ∈ twoCocycles G M) :
    pullC2 G M φ hφ c ∈ twoCocycles G' M := by
  rw [mem_twoCocycles] at hc ⊢
  intro g' h' k'
  simp only [pullC2_apply]
  rw [map_mul, map_mul, ← hφc, hc (φ g') (φ h') (φ k')]

/-- **`H⁰` の引き戻し** `M^G → M^{G'}`(`G`-不変は `G'`-不変)= restriction/inflation。 -/
def pullH0 : H0 G M →+ H0 G' M :=
  (H0 G M).subtype.codRestrict (H0 G' M) fun x => by
    rw [mem_H0]; intro g'
    rw [← hφc]; exact (mem_H0 G M).mp x.2 (φ g')

/-- 1-余輪体の引き戻し `Z¹(G,M) → Z¹(G',M)`。 -/
def pullZ1 : oneCocycles G M →+ oneCocycles G' M :=
  ((pullC1 G M φ hφ).comp (oneCocycles G M).subtype).codRestrict (oneCocycles G' M)
    fun x => pullC1_mem_oneCocycles G M φ hφ hφc x.2

/-- **`H¹` の引き戻し** `H¹(G,M) → H¹(G',M)`(restriction / inflation)。 -/
def pullH1 : H1 G M →+ H1 G' M :=
  QuotientAddGroup.map _ _ (pullZ1 G M φ hφ hφc) (by
    rintro x hx
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp hx)
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact AddMonoidHom.mem_range.mpr ⟨m, by
      show d0 G' M m = pullC1 G M φ hφ (x : C(G, M))
      rw [← pullC1_comp_d0 G M φ hφ hφc m, hm]⟩)

/-- 2-余輪体の引き戻し `Z²(G,M) → Z²(G',M)`。 -/
def pullZ2 : twoCocycles G M →+ twoCocycles G' M :=
  ((pullC2 G M φ hφ).comp (twoCocycles G M).subtype).codRestrict (twoCocycles G' M)
    fun x => pullC2_mem_twoCocycles G M φ hφ hφc x.2

/-- **`H²` の引き戻し** `H²(G,M) → H²(G',M)`。中心拡大の `φ` に沿う引き戻しに対応。 -/
def pullH2 : H2 G M →+ H2 G' M :=
  QuotientAddGroup.map _ _ (pullZ2 G M φ hφ hφc) (by
    rintro x hx
    obtain ⟨f, hf⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_addSubgroupOf.mp hx)
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact AddMonoidHom.mem_range.mpr ⟨pullC1 G M φ hφ f, by
      show d1 G' M (pullC1 G M φ hφ f) = pullC2 G M φ hφ (x : C(G × G, M))
      rw [← pullC2_comp_d1 G M φ hφ hφc f, hf]⟩)

end Restriction

/-! ## 自明作用の計算 ― `H⁰ = M`, `H¹ = 連続準同型`

`G` が `M` に自明に作用するとき(`g•m = m`)、連続群コホモロジーは具体対象を計算する:
`H⁰(G,M) = M`(全元不変)、`B¹ = 0` ゆえ `H¹(G,M) ≃ Hom_cont(G,M)`(連続準同型群)。
**円分指標** `G → Ẑ`(加法的には連続準同型)はまさにこの `H¹` 類として住む。 -/

section TrivialAction

variable (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-- 自明作用のもと `H⁰(G,M) = M`(全元が不変)。 -/
theorem H0_eq_top : H0 G M = ⊤ := by
  rw [eq_top_iff]; intro m _
  rw [mem_H0]; intro g; exact htriv g m

/-- 自明作用のもと `d⁰ = 0`。 -/
theorem d0_eq_zero : d0 G M = 0 := by
  ext m g
  simp only [d0_apply, htriv, sub_self, AddMonoidHom.zero_apply, ContinuousMap.zero_apply]

/-- 自明作用のもと `B¹ = 0`(余境界は自明)。 -/
theorem oneCoboundaries_eq_bot : oneCoboundaries G M = ⊥ := by
  show (d0 G M).range = ⊥
  exact AddMonoidHom.range_eq_bot_iff.mpr (d0_eq_zero G M htriv)

/-- 自明作用のもと 1-余輪体は **連続準同型**: `f(g·h) = f(g) + f(h)`。 -/
theorem mem_oneCocycles_trivial {f : C(G, M)} :
    f ∈ oneCocycles G M ↔ ∀ g h : G, f (g * h) = f g + f h := by
  rw [mem_oneCocycles]
  refine forall_congr' fun g => forall_congr' fun h => ?_
  rw [htriv, add_comm (f h) (f g)]

theorem coboundariesAddSubgroupOf_eq_bot :
    (oneCoboundaries G M).addSubgroupOf (oneCocycles G M) = ⊥ := by
  rw [oneCoboundaries_eq_bot G M htriv]
  ext x; simp [AddSubgroup.mem_addSubgroupOf]

/-- **自明作用のもと `H¹(G,M) ≃ Hom_cont(G,M)`**(`B¹=0` ゆえ `H¹ = Z¹ =` 連続準同型群)。
**円分指標** `G → Ẑ` がこの `H¹` 類として住む。 -/
noncomputable def trivialH1Equiv : H1 G M ≃+ oneCocycles G M :=
  (QuotientAddGroup.quotientAddEquivOfEq (coboundariesAddSubgroupOf_eq_bot G M htriv)).trans
    QuotientAddGroup.quotientBot

end TrivialAction

end IUT.Cohomology
