import Mathlib

/-!
# テータ群と交換子対 (Theta group / commutator pairing) — 単テータ剛性の代数的核

底本: [EtTh] (Mochizuki, *The Étale Theta Function ...*) §1, §5 / 星裕一郎『宇宙際
Teichmüller 理論入門』§14, §15。

エタールテータ関数 `Θ̈` を制御する **単テータ環境** (mono-theta environment) の心臓部は、
**テータ群** (theta group) と呼ばれる中心拡大

  `1 → Λ → G_θ → Π → 1`   (`Λ` = 円分物 `Ẑ(1)`、`Π` = 格子)

である。ここで `Λ` は `G_θ` の中心に含まれ、`G_θ` の **交換子** `⁅·,·⁆` は中心 `Λ` に値を取る
**双乗法的・交代的な対** `Π × Π → Λ` を誘導する。この交換子対こそが、

* **円分剛性** — 交換子対は群構造のみから定まり(関手的・正準的)、`Λ` を正準的に与える;
* **離散剛性** — 対の値が離散的構造で制御される;
* **定数倍剛性** — 中心 `Λ` 倍の不定性が交換子では消える(交換子は中心剰余に降下する)

の代数的源泉である ([EtTh] §5)。本モジュールでは、この交換子対の構造を **連続コホモロジーを
要さない純群論** として一から形式化する。`Λ` の値群としての具体化(`Ẑ(1)`)は
`IutLean.Cyclotome.Frobenius` の `FrobeniusCyclotome` が供給する。

主結果:
* `commutatorElement_mul_left` / `_right` — 交換子対の双乗法性(中心性から)。
* `commutatorElement_center_mul_left` / `_right` — 中心剰余 `Π = G/Z` への降下(定数倍剛性の核)。
* `thetaPairing` と `thetaPairingLeft` / `thetaPairingRight` — 中心値の対と、各成分の群準同型化。
* `thetaPairing_self` / `thetaPairing_swap` — 交代性(シンプレクティック構造)。
* `thetaPairing_naturality` — **関手性 = 円分剛性の核**:交換子対は任意の群準同型で保たれる。
-/

namespace IUT.Theta

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **テータ群** (theta group, [EtTh] §1)。交換子部分群が中心に含まれる群、すなわち
ベキ零度 `≤ 2`(Heisenberg 型)の中心拡大の全空間。交換子は中心値の双乗法的交代対を
誘導し、これが単テータ環境の円分剛性 ([EtTh] §5) の代数的核となる。 -/
class IsThetaGroup (G : Type*) [Group G] : Prop where
  /-- 任意の交換子 `⁅a,b⁆` は中心 `Z(G)`(= 円分物 `Λ`)に属する。 -/
  commutator_mem_center : ∀ a b : G, ⁅a, b⁆ ∈ center G

variable [IsThetaGroup G]

/-- 交換子は中心(円分物 `Λ`)に値を取る。 -/
theorem commutatorElement_mem_center (a b : G) : ⁅a, b⁆ ∈ center G :=
  IsThetaGroup.commutator_mem_center a b

/-- 中心元による共役は元を変えない: `z` が中心なら `g * z * g⁻¹ = z`。 -/
private theorem conj_center_eq (g : G) {z : G} (hz : z ∈ center G) :
    g * z * g⁻¹ = z := by
  rw [mem_center_iff.mp hz g, mul_inv_cancel_right]

/-- **交換子対の左双乗法性**: `⁅a*a', b⁆ = ⁅a,b⁆ * ⁅a',b⁆`。交換子が中心に属することによる
(中心拡大の交換子対が左成分について加法的であること)。 -/
theorem commutatorElement_mul_left (a a' b : G) :
    ⁅a * a', b⁆ = ⁅a, b⁆ * ⁅a', b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, conj_center_eq a (commutatorElement_mem_center a' b),
    mem_center_iff.mp (commutatorElement_mem_center a b) ⁅a', b⁆]

/-- **交換子対の右双乗法性**: `⁅a, b*b'⁆ = ⁅a,b⁆ * ⁅a,b'⁆`。 -/
theorem commutatorElement_mul_right (a b b' : G) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅a, b⁆ b ⁅a, b'⁆,
    mul_assoc ⁅a, b⁆ (b * ⁅a, b'⁆) b⁻¹, conj_center_eq b (commutatorElement_mem_center a b')]

/-- **左成分の中心剰余への降下**: `z` が中心なら `⁅a*z, b⁆ = ⁅a,b⁆`。すなわち交換子対は
格子 `Π = G/Z` 上の対に降下する(= 中心 `Λ` 倍の不定性が交換子で消える = 定数倍剛性の核)。 -/
theorem commutatorElement_center_mul_left (a b : G) {z : G} (hz : z ∈ center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left, commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp hz b).symm, mul_one]

/-- **右成分の中心剰余への降下**: `z` が中心なら `⁅a, b*z⁆ = ⁅a,b⁆`。 -/
theorem commutatorElement_center_mul_right (a b : G) {z : G} (hz : z ∈ center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right, commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp hz a), mul_one]

/-! ## 中心値の交換子対 `Π × Π → Λ` -/

/-- **交換子対** `G × G → Z(G)` ―― テータ群の中心(円分物 `Λ`)に値を取る対。 -/
def thetaPairing (a b : G) : center G :=
  ⟨⁅a, b⁆, commutatorElement_mem_center a b⟩

@[simp] theorem thetaPairing_coe (a b : G) : (thetaPairing a b : G) = ⁅a, b⁆ := rfl

/-- 固定した `b` に対し、`a ↦ ⁅a,b⁆` は群準同型 `G →* Z(G)`(双乗法性の左成分)。 -/
def thetaPairingLeft (b : G) : G →* center G where
  toFun a := thetaPairing a b
  map_one' := Subtype.ext (by simp [thetaPairing])
  map_mul' a a' := Subtype.ext (by
    rw [thetaPairing_coe, Subgroup.coe_mul, thetaPairing_coe, thetaPairing_coe,
      commutatorElement_mul_left])

/-- 固定した `a` に対し、`b ↦ ⁅a,b⁆` は群準同型 `G →* Z(G)`(双乗法性の右成分)。 -/
def thetaPairingRight (a : G) : G →* center G where
  toFun b := thetaPairing a b
  map_one' := Subtype.ext (by simp [thetaPairing])
  map_mul' b b' := Subtype.ext (by
    rw [thetaPairing_coe, Subgroup.coe_mul, thetaPairing_coe, thetaPairing_coe,
      commutatorElement_mul_right])

@[simp] theorem thetaPairingLeft_apply (a b : G) : thetaPairingLeft b a = thetaPairing a b := rfl

@[simp] theorem thetaPairingRight_apply (a b : G) : thetaPairingRight a b = thetaPairing a b := rfl

/-! ## 交代性(シンプレクティック構造) -/

/-- **交代性**: `⁅a,a⁆ = 1`、すなわち対角成分は自明。 -/
@[simp] theorem thetaPairing_self (a : G) : thetaPairing a a = 1 :=
  Subtype.ext (by simp [thetaPairing, commutatorElement_self])

/-- **反対称性**: `⁅a,b⁆ * ⁅b,a⁆ = 1`、すなわち `thetaPairing b a = (thetaPairing a b)⁻¹`。
交換子対がシンプレクティック(交代双線型)形式であることの内容。 -/
theorem thetaPairing_swap (a b : G) : thetaPairing a b * thetaPairing b a = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, thetaPairing_coe, thetaPairing_coe, Subgroup.coe_one,
      ← commutatorElement_inv, inv_mul_cancel])

theorem thetaPairing_inv (a b : G) : (thetaPairing a b)⁻¹ = thetaPairing b a :=
  (eq_inv_of_mul_eq_one_right (thetaPairing_swap a b)).symm

/-! ## 関手性 = 円分剛性の核 -/

/-- **交換子対の関手性 (= 円分剛性の核)**: 任意の群準同型 `f : G →* G'` は交換子対を保つ:
`f ⁅a,b⁆ = ⁅f a, f b⁆`。これは「交換子対(従って円分物 `Λ`)が群構造のみから正準的・
関手的に定まる」という **円分剛性** の代数的本質である。Kummer 類などの選択を一切要しない。 -/
theorem thetaPairing_naturality {G' : Type*} [Group G'] (f : G →* G') (a b : G) :
    f ⁅a, b⁆ = ⁅f a, f b⁆ :=
  map_commutatorElement f a b

/-- 同型 `e : G ≃* G'`(両者テータ群)は交換子対を保ち、中心 `Λ` を正準的に対応させる。
円分剛性の同型版。 -/
theorem thetaPairing_congr {G' : Type*} [Group G'] [IsThetaGroup G'] (e : G ≃* G') (a b : G) :
    (e (thetaPairing a b) : G') = thetaPairing (e a) (e b) := by
  rw [thetaPairing_coe, thetaPairing_coe, map_commutatorElement]

/-! ## テータ的円分物 `Λ = ∆_Θ`(交換子で生成される中心部分群) -/

/-- **テータ的円分物** `∆_Θ` の代数的実現: テータ群の交換子部分群 `⁅G,G⁆`。仮定により中心に
含まれ(従って可換)、交換子対 `thetaPairing` の像が生成する。これが単テータ環境における
円分物 `Λ`(`Ẑ(1)`)の群論的座席である。 -/
theorem commutator_le_center : commutator G ≤ center G := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x hx
  rw [mem_commutatorSet_iff] at hx
  obtain ⟨a, b, rfl⟩ := hx
  exact commutatorElement_mem_center a b

/-- テータ的円分物 `⁅G,G⁆` は可換(中心に含まれるため)。 -/
instance : IsMulCommutative (commutator G) :=
  IsMulCommutative.of_comm fun x y => Subtype.ext (by
    have hx := mem_center_iff.mp (commutator_le_center (G := G) x.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx])

/-! ## 可換群はテータ群(自明な例) -/

/-- 可換群は自明なテータ群(交換子がすべて `1` ∈ 中心)。 -/
instance (priority := 100) {G : Type*} [CommGroup G] : IsThetaGroup G where
  commutator_mem_center a b := by
    rw [commutatorElement_eq_one_iff_commute.mpr (mul_comm a b)]
    exact one_mem _

end IUT.Theta
