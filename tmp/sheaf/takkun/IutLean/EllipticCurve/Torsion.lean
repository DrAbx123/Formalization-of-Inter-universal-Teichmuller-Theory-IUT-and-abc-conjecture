import Mathlib

/-!
# 楕円曲線の `n`-等分点 (Track B / [IUT-I] Def 3.1(b),(c))

底本: [IUT-I] Definition 3.1 (b),(c), 星裕一郎入門 §17。

初期 Θ データの条件には、楕円曲線 `E` の等分点に関わるものがある:
* **(b)** `E` の `2·3 = 6`-等分点が `F`-有理的、
* **(c)** `l`-等分点が定める Galois 表現 `G_F → GL₂(F_l)` の像が `SL₂(F_l)` を含む。

本ファイルでは、Mathlib の楕円曲線の点群 `W.toAffine.Point`(`AddCommGroup`)を用いて
**`n`-等分部分群** `W[n] = {P | n • P = 0}` を構成し、基本性質(`m ∣ n ⟹ W[m] ≤ W[n]`)を
`sorry` 無しに証明する。これにより条件 (b) の `SixTorsionRational` を**具体的な命題**
(`|W(F)[6]| = 36`)として与える(Track B)。
-/

namespace IUT.EllipticCurve

open WeierstrassCurve

/-- `n` 倍写像 `G → G`(`g ↦ n • g`)を加法群準同型として束ねたもの。 -/
def smulN (G : Type*) [AddCommGroup G] (n : ℕ) : G →+ G where
  toFun g := n • g
  map_zero' := smul_zero n
  map_add' := smul_add n

@[simp] theorem smulN_apply {G : Type*} [AddCommGroup G] (n : ℕ) (g : G) :
    smulN G n g = n • g := rfl

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- **`n`-等分部分群** `W[n] = {P ∈ W(F) | n • P = 0}`。`n` 倍写像の核として定義する。 -/
def nTorsion (n : ℕ) : AddSubgroup W.toAffine.Point :=
  (smulN W.toAffine.Point n).ker

/-- `P` が `n`-等分点 ⟺ `n • P = 0`。 -/
theorem mem_nTorsion {n : ℕ} {P : W.toAffine.Point} :
    P ∈ nTorsion W n ↔ n • P = 0 := by
  rw [nTorsion, AddMonoidHom.mem_ker, smulN_apply]

/-- 零点は常に `n`-等分点。 -/
theorem zero_mem_nTorsion (n : ℕ) : (0 : W.toAffine.Point) ∈ nTorsion W n :=
  (nTorsion W n).zero_mem

/-- **等分の単調性**: `m ∣ n` ならば `W[m] ≤ W[n]`(`m`-等分点は `n`-等分点)。 -/
theorem nTorsion_mono {m n : ℕ} (h : m ∣ n) : nTorsion W m ≤ nTorsion W n := by
  obtain ⟨k, rfl⟩ := h
  intro P hP
  rw [mem_nTorsion] at hP ⊢
  rw [mul_comm, mul_smul, hP, smul_zero]

/-- **[IUT-I] Def 3.1(b) の `SixTorsionRational` の具体化**(Track B): `E` の `2·3 = 6`-等分点が
すべて `F`-有理的、すなわち `F`-有理な 6-等分点の個数が `6² = 36`(完全 6-等分が `F` 上で実現)。
旧 `opaque IUT.SixTorsionRational` を、この**具体的命題**に置き換える。 -/
def SixTorsionRational : Prop := Nat.card (nTorsion W 6) = 36

/-! ## `F_l`-加群構造(mod-`l` Galois 表現の土台, Track B / Def 3.1(c)) -/

/-- `n`-等分部分群の元は `n` 倍で消える。 -/
theorem nsmul_eq_zero_of_mem_nTorsion (n : ℕ) (x : nTorsion W n) : n • x = 0 := by
  refine Subtype.ext ?_
  have hx : n • (x : W.toAffine.Point) = 0 := (mem_nTorsion W).mp x.2
  simpa using hx

/-- **`n`-等分点は `ZMod n`-加群**。特に `l`-等分点 `W[l]` は `F_l = ℤ/l` 上のベクトル空間であり、
これが mod-`l` Galois 表現 `G_F → GL(W[l]) ≅ GL₂(F_l)`([IUT-I] Def 3.1(c) の `ContainsSL2Image`)の
**出発点**となる。(`ContainsSL2Image` の完全な定式化には、さらに幾何的等分点 `E[l] ≅ (ℤ/l)²`
(`F̄` 上)とその Galois 作用 ―― Mathlib 未整備 ―― が必要。) -/
noncomputable instance instModuleZModNTorsion (n : ℕ) [NeZero n] :
    Module (ZMod n) (nTorsion W n) :=
  AddCommMonoid.zmodModule (nsmul_eq_zero_of_mem_nTorsion W n)

end IUT.EllipticCurve
