import Mathlib
import tmp.sheaf.takkun.IutLean.Cyclotome.Kummer
import tmp.sheaf.takkun.IutLean.Arithmetic.RealHodgeTheater

/-!
# 実 Kummer 類 — 実 Hodge 劇場上の theta/Kummer 両立性(最終脱ブラックボックス化)

底本: [IUT-II] §3・Cor 4.6/4.8(テータ値・q-parameter の Kummer 理論)、
[IUT-III] Thm 3.11 (ii)(log-Kummer 対応)。

`HasPrimeStripSystem` の脱ブラックボックス化(`HodgeTheater/PrimeStripData.lean`)に
残されていた懸念は「**theta/Kummer 両立性**(テータ値の Kummer 理論が素点縞の Galois
構造と両立すること)が構造に含まれていない」ことだった。本モジュールはその機構を
**実対象の上で実際に構成**する:

## 証明済(全て標準公理のみ)

* `galoisUnitsAction_fixes_qParam`: 実 q-parameter(`= p ∈ ℚ̄_pˣ`)は実 Galois 群
  `Gal(ℚ̄_p/ℚ_p)` で固定される(`map_natCast`);
* `realQRootSystem` / `realThetaRootSystem`: 実 q-parameter と**全テータ値 `q^{j²}`** の
  両立的巾根系(`ℚ̄_p` 代数閉 + 階乗鎖 `Cyclotome/Kummer.lean`; テータ値の巾根系は
  q の巾根系の巾 `RootSystem.pow` で一斉に得られる);
* `realQKummer` / `realThetaKummer`: **実 Kummer 類** ―― 実 Galois 群上の
  円分物 `Λ(ℚ̄_pˣ)` 値写像;
* **`realThetaKummer_cocycle`(theta/Kummer 両立性、capstone)**: 全テータ値の
  Kummer 類は、素点縞系 `realPrimeStripSystem` 自身の Kummer 円分指標
  (`PrimeStripSystem.kummer` = `cyclotomicCharacter`)に関して **1-コサイクル**である
  ―― Frobenius 的対象(テータ値)とエタール的対象(Galois 円分物)が
  **実際の機構で**両立している。これが [IUT-II] の Kummer 理論の核心の実現であり、
  `PrimeStripData.lean` の docstring が「under-statement を避けるため含めなかった」
  両立性の、正直な形式化である。

## 残余(honest)

* Kummer **同型**への昇格(`H¹` の同定、Hilbert 90、円分剛性同型 `Λ(M) ≅ Λ(G)`);
* log-Kummer 対応([IUT-III] Thm 3.11 (ii))の「1 の巾根 ↦ 0」条項との配線
  (対数リンクの実対象上の芽 `Padic/ComplexLog.lean` との合成);
* 実 Galois 群上の Kummer 類の非自明性(`ℚ_p(p^{1/n})/ℚ_p` の分岐)。
-/

namespace IUT.Arithmetic

open IUT.Cyclotome

variable (p : ℕ) [hp : Fact p.Prime]

/-- 素数 `p` の定める有理素点。 -/
def thePlace : RationalPlaces := ⟨p, hp.out⟩

/-- **実 Galois 群は実 q-parameter を固定する**: `q = p ∈ ℚ_p ⊂ ℚ̄_p` は
`Gal(ℚ̄_p/ℚ_p)` の作用で不変(`σ(↑p) = ↑p`)。Kummer 類の構成の前提。 -/
theorem galoisUnitsAction_fixes_qParam (σ : LocalGalois p) :
    galoisUnitsAction p σ (realGaussianStrip.qParam (thePlace p))
      = realGaussianStrip.qParam (thePlace p) := by
  apply Units.ext
  change σ (((p : ℕ) : AlgebraicClosure ℚ_[p])) = ((p : ℕ) : AlgebraicClosure ℚ_[p])
  exact map_natCast σ p

/-- **実 q-parameter の両立的巾根系**(`ℚ̄_p` 代数閉 + 階乗鎖による構成)。 -/
noncomputable def realQRootSystem :
    RootSystem (M := (AlgebraicClosure ℚ_[p])ˣ) (realGaussianStrip.qParam (thePlace p)) :=
  rootSystemOfAlgClosed _

/-- **実 q-parameter の Kummer 類**: `σ ↦ (σ(q^{1/n})/q^{1/n})_n ∈ Λ(ℚ̄_pˣ)`。 -/
noncomputable def realQKummer (σ : LocalGalois p) :
    FrobeniusCyclotome ((AlgebraicClosure ℚ_[p])ˣ) :=
  kummerClass (galoisUnitsAction p) (realQRootSystem p)
    (galoisUnitsAction_fixes_qParam p) σ

/-- 実 q-parameter の Kummer 類のコサイクル律(`cyclotomicAut` 形)。 -/
theorem realQKummer_cocycle (σ τ : LocalGalois p) :
    realQKummer p (σ * τ)
      = cyclotomicAut ((AlgebraicClosure ℚ_[p])ˣ) (galoisUnitsAction p σ)
          (realQKummer p τ) * realQKummer p σ :=
  kummerClass_mul (galoisUnitsAction p) (realQRootSystem p)
    (galoisUnitsAction_fixes_qParam p) σ τ

/-! ## 全テータ値への拡張 -/

/-- **実 Galois 群は全テータ値を固定する**(`q^{j²}` は固定元の巾)。 -/
theorem galoisUnitsAction_fixes_thetaValue (j : ℤ) (σ : LocalGalois p) :
    galoisUnitsAction p σ (realGaussianStrip.thetaValueAt (thePlace p) j)
      = realGaussianStrip.thetaValueAt (thePlace p) j :=
  fixes_pow (galoisUnitsAction p) (galoisUnitsAction_fixes_qParam p)
    (IUT.Theta.gaussExp j).toNat σ

/-- **全テータ値の両立的巾根系**: q-parameter の巾根系の巾(`RootSystem.pow`)として
一斉に得られる ―― Gaussian 単項式 `{q^{j²}}` の Kummer 理論が単一の巾根系から
生成されること([IUT-II] の「テータ値の Kummer 理論」の仕組み)。 -/
noncomputable def realThetaRootSystem (j : ℤ) :
    RootSystem (M := (AlgebraicClosure ℚ_[p])ˣ)
      (realGaussianStrip.thetaValueAt (thePlace p) j) := by
  change RootSystem (M := (AlgebraicClosure ℚ_[p])ˣ)
    (realGaussianStrip.qParam (thePlace p) ^ (IUT.Theta.gaussExp j).toNat)
  exact (realQRootSystem p).pow _

/-- **全テータ値の実 Kummer 類**。 -/
noncomputable def realThetaKummer (j : ℤ) (σ : LocalGalois p) :
    FrobeniusCyclotome ((AlgebraicClosure ℚ_[p])ˣ) :=
  kummerClass (galoisUnitsAction p) (realThetaRootSystem p j)
    (galoisUnitsAction_fixes_thetaValue p j) σ

/-- **素点縞系の Kummer 円分指標の実型での読み**: `realPrimeStripSystem` の
`PrimeStripSystem.kummer`(テータ値モノイドの Galois 作用が円分物に誘導する作用)を、
素点 `p` で実際の型 `MulAut (Λ(ℚ̄_pˣ))` として読んだもの(定義的に等しい ――
`realSystemKummer_eq`)。 -/
noncomputable def realSystemKummer (l : ℕ) [Fact l.Prime] (σ : LocalGalois p) :
    MulAut (FrobeniusCyclotome ((AlgebraicClosure ℚ_[p])ˣ)) :=
  (realPrimeStripSystem l).kummer (thePlace p) σ

/-- 素点縞系の Kummer 円分指標は、円分指標 `cyclotomicAut` による実 Galois 作用の
持ち上げに**定義的に**一致する。 -/
theorem realSystemKummer_eq (l : ℕ) [Fact l.Prime] (σ : LocalGalois p) :
    realSystemKummer p l σ
      = cyclotomicAut ((AlgebraicClosure ℚ_[p])ˣ) (galoisUnitsAction p σ) := rfl

/-- **theta/Kummer 両立性(capstone、最終脱ブラックボックス化)**: 実素点縞系
`realPrimeStripSystem l` の **Kummer 円分指標**(`PrimeStripSystem.kummer` =
テータ値のモノイドへの Galois 作用が円分物 `Λ(ℚ̄_pˣ)` に誘導する作用)に関して、
**全テータ値の Kummer 類は 1-コサイクル**である:
`c_j(στ) = kummer(σ)·c_j(τ) · c_j(σ)`。

これは「素点縞の Frobenius 的データ(テータ値)とエタール的データ(Galois 円分物)が
Kummer 理論で両立する」という [IUT-II] Cor 4.6/4.8 の機構の、実対象
(実 Galois 群 `Gal(ℚ̄_p/ℚ_p)`・実代数閉包・実テータ値 `p^{j²}`)上での実現であり、
旧 `opaque HasPrimeStripSystem` の脱ブラックボックス化で「含めると under-statement に
なる」として据え置かれていた theta/Kummer 両立性の、機構による正直な充足である。 -/
theorem realThetaKummer_cocycle (l : ℕ) [Fact l.Prime] (j : ℤ) (σ τ : LocalGalois p) :
    realThetaKummer p j (σ * τ)
      = realSystemKummer p l σ (realThetaKummer p j τ) * realThetaKummer p j σ :=
  kummerClass_mul (galoisUnitsAction p) (realThetaRootSystem p j)
    (galoisUnitsAction_fixes_thetaValue p j) σ τ

/-- q-parameter 版の capstone(`j` 抜きの基底形): q-標対象の Kummer 類も
素点縞系の Kummer 円分指標に関するコサイクル。 -/
theorem realQKummer_cocycle_system (l : ℕ) [Fact l.Prime] (σ τ : LocalGalois p) :
    realQKummer p (σ * τ)
      = realSystemKummer p l σ (realQKummer p τ) * realQKummer p σ :=
  kummerClass_mul (galoisUnitsAction p) (realQRootSystem p)
    (galoisUnitsAction_fixes_qParam p) σ τ

end IUT.Arithmetic
