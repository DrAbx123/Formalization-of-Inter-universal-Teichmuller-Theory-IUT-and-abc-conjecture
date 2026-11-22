import Mathlib
import tmp.sheaf.takkun.IutLean.EllipticCurve.Torsion

/-!
# mod-`l` Galois 表現の本格構築 (Track B / [IUT-I] Def 3.1(c))

底本: [IUT-I] Definition 3.1 (c)(`l`-等分表現の像が `SL₂(F_l)` を含む)。

楕円曲線 `E/k` と Galois 拡大 `K/k` に対し、Galois 群 `K ≃ₐ[k] K` は幾何的点 `E(K)` に作用する。
Mathlib の点群の関手性 `WeierstrassCurve.Affine.Point.map`(代数写像 `K →ₐ[k] K` に沿う加法群
準同型)を用いて、この **Galois 作用** を構成する。
-/

namespace IUT.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K] [DecidableEq K]
  (W : Affine k)

/-- Galois 自己同型 `σ : K ≃ₐ[k] K` が幾何的点 `E(K)` に誘導する**加法的自己同型**。
点群の関手性 `Point.map` を `σ` とその逆で組むことで得る。 -/
noncomputable def galoisPointMap (σ : K ≃ₐ[k] K) : Point (W⁄K) ≃+ Point (W⁄K) where
  toFun := Point.map σ.toAlgHom
  invFun := Point.map σ.symm.toAlgHom
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h => simp [Point.map_some]
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h => simp [Point.map_some]
  map_add' := (Point.map σ.toAlgHom).map_add

@[simp] theorem galoisPointMap_apply (σ : K ≃ₐ[k] K) (P : Point (W⁄K)) :
    galoisPointMap W σ P = Point.map σ.toAlgHom P := rfl

/-- **Galois 作用 / mod-`l` Galois 表現**: `Gal(K/k) = (K ≃ₐ[k] K)` が幾何的点 `E(K)` に
分配的に作用する(`σ • (P+Q) = σ•P + σ•Q`)。これが mod-`l` Galois 表現
`G_k → GL(E[l])`([IUT-I] Def 3.1(c))の出発点。
(Mathlib では `AddAut M` は*加法*群のため、表現は `DistribMulAction` として与えるのが自然。) -/
noncomputable instance galoisAction : DistribMulAction (K ≃ₐ[k] K) (Point (W⁄K)) where
  smul σ P := galoisPointMap W σ P
  one_smul P := by
    show galoisPointMap W 1 P = P
    cases P with
    | zero => rfl
    | some x y h => simp [Point.map_some]
  mul_smul σ τ P := by
    show galoisPointMap W (σ * τ) P = galoisPointMap W σ (galoisPointMap W τ P)
    cases P with
    | zero => rfl
    | some x y h => simp [Point.map_some, AlgEquiv.mul_apply]
  smul_zero σ := rfl
  smul_add σ P Q := (galoisPointMap W σ).map_add P Q

/-- **Galois 作用は `l`-等分点 `E[l]` を保つ**。よって `Gal(K/k)` は `E[l]` に作用し、
mod-`l` Galois 表現 `G_k → GL(E[l]) ≅ GL₂(F_l)`([IUT-I] Def 3.1(c))が得られる。 -/
theorem smul_mem_nTorsion (σ : K ≃ₐ[k] K) {n : ℕ} {P : Point (W⁄K)}
    (hP : P ∈ nTorsion (W⁄K) n) : σ • P ∈ nTorsion (W⁄K) n := by
  rw [mem_nTorsion] at hP ⊢
  show n • galoisPointMap W σ P = 0
  rw [← map_nsmul, hP, map_zero]

/-! ## mod-`l` Galois 表現 `G_k → GL(E[l])` と `ContainsSL2Image` -/

variable (l : ℕ) [NeZero l]

/-- Galois 作用の `E[l]` への制限(`Gal(K/k)` が `l`-等分点に作用)。 -/
noncomputable instance galoisTorsionAction :
    DistribMulAction (K ≃ₐ[k] K) (nTorsion (W⁄K) l) where
  smul σ x := ⟨σ • (x : Point (W⁄K)), smul_mem_nTorsion W σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul σ τ x := Subtype.ext (mul_smul _ _ _)
  smul_zero σ := Subtype.ext (smul_zero _)
  smul_add σ x y := Subtype.ext (smul_add _ _ _)

/-- Galois 作用は `E[l]` の `F_l = ZMod l`-加群構造と可換(= `F_l`-線型)。
加法写像が ZMod 線型であること(`ZMod.map_smul`)による。 -/
instance galoisTorsion_smulComm :
    SMulCommClass (K ≃ₐ[k] K) (ZMod l) (nTorsion (W⁄K) l) where
  smul_comm σ c x := ZMod.map_smul (DistribMulAction.toAddMonoidHom _ σ) c x

/-- **mod-`l` Galois 表現** `ρ : Gal(K/k) → GL(E[l])` ―― `E[l]` の `F_l`-線型自己同型への
群準同型。[IUT-I] Def 3.1(c) の Galois 表現そのもの。 -/
noncomputable def galoisRepMod : (K ≃ₐ[k] K) →* (nTorsion (W⁄K) l ≃ₗ[ZMod l] nTorsion (W⁄K) l) :=
  DistribMulAction.toModuleAut (ZMod l) (nTorsion (W⁄K) l)

/-- 表現 `ρ(σ)` は `E[l]` 上の Galois 作用そのもの。 -/
@[simp] theorem galoisRepMod_apply (σ : K ≃ₐ[k] K) (x : nTorsion (W⁄K) l) :
    galoisRepMod W l σ x = σ • x := rfl

/-- 表現の像にはまず恒等写像(`σ = 1`)が入る。 -/
theorem one_mem_range_galoisRepMod :
    (1 : nTorsion (W⁄K) l ≃ₗ[ZMod l] nTorsion (W⁄K) l) ∈ Set.range (galoisRepMod W l) :=
  ⟨1, map_one _⟩

/-- **[IUT-I] Def 3.1(c) の `ContainsSL2Image` の具体化**: mod-`l` Galois 表現
`ρ : Gal(K/k) → GL(E[l])` の像が `SL₂(F_l)` を含むこと ―― すなわち、行列式 `1` の `F_l`-線型
自己同型はすべて `ρ` の像に入る(行列式 `1` の自己同型全体 = `SL₂(F_l)` を基底に依らず内在的に表現)。 -/
def ContainsSL2Image : Prop :=
  ∀ φ : nTorsion (W⁄K) l ≃ₗ[ZMod l] nTorsion (W⁄K) l,
    LinearMap.det (φ : nTorsion (W⁄K) l →ₗ[ZMod l] nTorsion (W⁄K) l) = 1 →
      φ ∈ Set.range (galoisRepMod W l)

open Classical in
/-- 数体 `F` 上の楕円曲線に対し、代数閉包 `F̄`(その絶対 Galois 群 `Gal(F̄/F)`)を用いた
`ContainsSL2Image` = [IUT-I] Def 3.1(c)。`E[l]` への mod-`l` Galois 表現の像が `SL₂(F_l)` を含む。 -/
noncomputable def ContainsSL2ImageAlgClosure {F : Type*} [Field F] (E : WeierstrassCurve F)
    (l : ℕ) [NeZero l] : Prop :=
  ContainsSL2Image (K := AlgebraicClosure F) E.toAffine l

end IUT.EllipticCurve
