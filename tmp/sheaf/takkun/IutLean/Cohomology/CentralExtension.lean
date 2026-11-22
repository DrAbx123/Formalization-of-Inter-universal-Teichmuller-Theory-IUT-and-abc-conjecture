import Mathlib
import tmp.sheaf.takkun.IutLean.Theta.ThetaGroup

/-!
# 中心拡大の因子団と 2-余輪体 (Factor set of a central extension)

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§1 / Mochizuki [AbsTopIII]。

第 2 群コホモロジー `H²(G,A)` が **中心拡大** `1 → A → E → G → 1` を分類することの核心は、
全射準同型 `π : E →* G` の(集合論的)**切断** `s : G → E` から定まる **因子団 (factor set)**

  `c(g,h) := s(g) · s(h) · s(g·h)⁻¹`

が、核 `ker π`(中心)に値を取り、**2-余輪体の恒等式**を満たすことにある。本モジュールでは、
この純群論的事実を `sorry` 無しで証明する。これは IUT の**テータ群** `1→Λ→Gθ→Π→1`
(`IUT.Theta.IsThetaGroup`、Phase C2)が定める `H²` 類 ―― 円分剛性の代数的機構 ―― の基盤であり、
連続版コホモロジー(`IutLean.Cohomology.Continuous` の `twoCocycles`、Phase C3)と接続する。

主結果:
* `factorSet_mem_ker` ―― 因子団は核に値を取る(`π(c(g,h)) = 1`)。
* `factorSet_cocycle` ―― **2-余輪体恒等式** `c(g,h)·c(g·h,k) = c(h,k)·c(g,h·k)`
  (中心拡大の結合律 / 因子系の整合条件)。
-/

namespace IUT.Cohomology

section CentralExtension

variable {E G : Type*} [Group E] [Group G] (s : G → E)

/-- 中心拡大の切断 `s` から定まる **因子団** `c(g,h) = s(g)·s(h)·s(g·h)⁻¹`。 -/
def factorSet (g h : G) : E := s g * s h * (s (g * h))⁻¹

/-- 因子団は核 `ker π` に値を取る: `π(c(g,h)) = g·h·(g·h)⁻¹ = 1`。 -/
theorem factorSet_mem_ker (π : E →* G) (hs : Function.RightInverse s π) (g h : G) :
    factorSet s g h ∈ π.ker := by
  rw [MonoidHom.mem_ker, factorSet, map_mul, map_mul, map_inv, hs g, hs h, hs (g * h)]
  group

/-- **因子団の 2-余輪体恒等式**(中心拡大の結合律):
`c(g,h) · c(g·h,k) = c(h,k) · c(g,h·k)`。核が中心であること(`hc`)と結合律から従う。
加法的に書けば `c(g,h) + c(g·h,k) = c(h,k) + c(g,h·k)`、すなわち
`IUT.Cohomology.mem_twoCocycles`(自明作用)の 2-余輪体条件そのもの。 -/
theorem factorSet_cocycle (π : E →* G) (hs : Function.RightInverse s π)
    (hc : ∀ z ∈ π.ker, ∀ e : E, z * e = e * z) (g h k : G) :
    factorSet s g h * factorSet s (g * h) k = factorSet s h k * factorSet s g (h * k) := by
  have hcomm : factorSet s h k * s g = s g * factorSet s h k :=
    hc _ (factorSet_mem_ker s π hs h k) (s g)
  have hL : factorSet s g h * factorSet s (g * h) k = s g * s h * s k * (s (g * h * k))⁻¹ := by
    simp only [factorSet]; group
  have hR : factorSet s h k * factorSet s g (h * k) = s g * s h * s k * (s (g * h * k))⁻¹ := by
    rw [show factorSet s g (h * k) = s g * s (h * k) * (s (g * h * k))⁻¹ by
          rw [factorSet, ← mul_assoc g h k]]
    rw [← mul_assoc (factorSet s h k), ← mul_assoc (factorSet s h k), hcomm]
    simp only [factorSet]; group
  rw [hL, hR]

end CentralExtension

/-! ## テータ群との接続 ― 中心部分群による商は中心拡大 -/

/-- 中心部分群 `Z ≤ Z(Gθ)` による商 `Gθ → Gθ/Z` は **核が中心**。よって任意の切断から
因子団(`factorSet`)= `H²(Gθ/Z, Z)` 類が定まる。Phase C2 の**テータ群**
`1→Λ→Gθ→Π→1`(`IsThetaGroup Gθ`: 交換子部分群 ⊆ 中心)は `Z = ⁅Gθ,Gθ⁆`(`commutator_le_center`)
としてこの状況にあり、単テータ環境の円分剛性 `H²` 類を与える。 -/
theorem center_quotient_ker_central (Gθ : Type*) [Group Gθ] (Z : Subgroup Gθ) [Z.Normal]
    (hZ : Z ≤ Subgroup.center Gθ) :
    ∀ z ∈ (QuotientGroup.mk' Z).ker, ∀ e : Gθ, z * e = e * z := by
  intro z hz e
  rw [QuotientGroup.ker_mk'] at hz
  exact (Subgroup.mem_center_iff.mp (hZ hz) e).symm

/-- **テータ群が定める中心拡大**: `IsThetaGroup Gθ` のとき、交換子部分群 `⁅Gθ,Gθ⁆` による商
`Gθ → Gθ/⁅Gθ,Gθ⁆` は核が中心。`factorSet_cocycle` と合わせ、テータ群の切断は `H²` の
2-余輪体(円分剛性の因子団)を与える。 -/
theorem thetaGroup_commutator_ker_central (Gθ : Type*) [Group Gθ] [Theta.IsThetaGroup Gθ] :
    ∀ z ∈ (QuotientGroup.mk' (commutator Gθ)).ker, ∀ e : Gθ, z * e = e * z :=
  center_quotient_ker_central Gθ (commutator Gθ) Theta.commutator_le_center

/-! ## 逆向き ― 2-余輪体から中心拡大を構成(`H²` 分類の構成的方向)

正規化された 2-余輪体 `c : G → G → A`(`A` 加法的アーベル群、自明作用)から、台集合 `A × G` に
**ねじった群演算** `(a,g)·(b,h) = (a + b + c(g,h), g·h)` を入れると群になる。**結合律が成り立つこと
が、ちょうど 2-余輪体恒等式 `c(g,h)+c(gh,k) = c(h,k)+c(g,hk)` と同値**である。これが
`H²(G,A)` が中心拡大を分類することの構成的方向であり、`factorSet`(前節)と逆の対応を与える。 -/

section OfCocycle

variable {G A : Type*} [Group G] [AddCommGroup A]

/-- **正規化された 2-余輪体**: 余輪体恒等式と正規化条件 `c(1,g)=c(g,1)=0`。 -/
class IsNormalizedCocycle (c : G → G → A) : Prop where
  cocycle : ∀ g h k, c g h + c (g * h) k = c h k + c g (h * k)
  normLeft : ∀ g, c 1 g = 0
  normRight : ∀ g, c g 1 = 0

/-- 2-余輪体 `c` から定まる中心拡大の台 `A × G`(`c` でねじった群)。`c` は phantom パラメータ
(インスタンス解決のため型に持たせる)。 -/
@[ext] structure Extension (c : G → G → A) where
  /-- `A`(核 = 中心)成分。 -/
  coeff : A
  /-- `G`(底)成分。 -/
  base : G

namespace Extension

variable {c : G → G → A} [IsNormalizedCocycle c]

instance : Group (Extension c) where
  mul x y := ⟨x.coeff + y.coeff + c x.base y.base, x.base * y.base⟩
  one := ⟨0, 1⟩
  inv x := ⟨-x.coeff - c x.base x.base⁻¹, x.base⁻¹⟩
  mul_assoc x y z := by
    refine Extension.ext ?_ ?_
    · change x.coeff + y.coeff + c x.base y.base + z.coeff + c (x.base * y.base) z.base
          = x.coeff + (y.coeff + z.coeff + c y.base z.base) + c x.base (y.base * z.base)
      have hco := IsNormalizedCocycle.cocycle (c := c) x.base y.base z.base
      rw [show x.coeff + y.coeff + c x.base y.base + z.coeff + c (x.base * y.base) z.base
            = x.coeff + y.coeff + z.coeff
              + (c x.base y.base + c (x.base * y.base) z.base) from by abel, hco]
      abel
    · change x.base * y.base * z.base = x.base * (y.base * z.base)
      exact mul_assoc _ _ _
  one_mul x := by
    refine Extension.ext ?_ ?_
    · change (0 : A) + x.coeff + c 1 x.base = x.coeff
      rw [IsNormalizedCocycle.normLeft (c := c)]; abel
    · change (1 : G) * x.base = x.base
      exact one_mul _
  mul_one x := by
    refine Extension.ext ?_ ?_
    · change x.coeff + 0 + c x.base 1 = x.coeff
      rw [IsNormalizedCocycle.normRight (c := c)]; abel
    · change x.base * 1 = x.base
      exact mul_one _
  inv_mul_cancel x := by
    refine Extension.ext ?_ ?_
    · change -x.coeff - c x.base x.base⁻¹ + x.coeff + c x.base⁻¹ x.base = (0 : A)
      have h := IsNormalizedCocycle.cocycle (c := c) x.base x.base⁻¹ x.base
      rw [mul_inv_cancel, inv_mul_cancel, IsNormalizedCocycle.normLeft (c := c),
        IsNormalizedCocycle.normRight (c := c), add_zero, add_zero] at h
      rw [h]; abel
    · change x.base⁻¹ * x.base = (1 : G)
      exact inv_mul_cancel _

@[simp] lemma mul_coeff (x y : Extension c) :
    (x * y).coeff = x.coeff + y.coeff + c x.base y.base := rfl
@[simp] lemma mul_base (x y : Extension c) : (x * y).base = x.base * y.base := rfl
@[simp] lemma one_coeff : (1 : Extension c).coeff = 0 := rfl
@[simp] lemma one_base : (1 : Extension c).base = 1 := rfl

/-- 射影 `π : Extension c →* G`(中心拡大の全射)。 -/
def proj : Extension c →* G where
  toFun x := x.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- 標準切断 `s : G → Extension c`, `g ↦ (0, g)`。 -/
def sec (g : G) : Extension c := ⟨0, g⟩

@[simp] lemma proj_sec (g : G) : proj (sec (c := c) g) = g := rfl

/-- **対応の閉包**: 構成した中心拡大 `Extension c` の標準切断 `sec` の因子団が `c` を回復する:
`(factorSet sec g h).coeff = c(g,h)`、`base = 1`。すなわち `factorSet ∘ (cocycle→extension) = id`。 -/
theorem factorSet_sec_coeff (g h : G) :
    (factorSet (sec (c := c)) g h).coeff = c g h := by
  change (0 + 0 + c g h) + (-0 - c (g * h) (g * h)⁻¹) + c (g * h) (g * h)⁻¹ = c g h
  abel

theorem factorSet_sec_base (g h : G) :
    (factorSet (sec (c := c)) g h).base = 1 := by
  change g * h * (g * h)⁻¹ = 1
  exact mul_inv_cancel _

end Extension

end OfCocycle

end IUT.Cohomology
