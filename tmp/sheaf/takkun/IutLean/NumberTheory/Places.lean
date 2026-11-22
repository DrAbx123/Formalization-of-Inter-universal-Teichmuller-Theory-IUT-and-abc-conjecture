import Mathlib

/-!
# 数体の素点と付値の切断 (Track A / [IUT-I] Def 3.1(e))

底本: [IUT-I] Definition 3.1 (e), 星裕一郎入門 §17。

初期 Θ データの条件 (e) は、`V ⊆ V(K)` が自然な全射 `V(K) ↠ V_mod` の**切断**の像であって
全単射 `V ≅ V_mod` を誘導する、というものである。本ファイルでは、この条件の核を:

1. **抽象原理**: 全射には切断が存在し、切断は単射(`V ≅ V_mod`)であること、
2. **整拡大への具体化**: 数体 `K/F` の整数環 `𝓞_F → 𝓞_K`(整な単射拡大)に対し、素点の
   制限 `Spec 𝓞_K ↠ Spec 𝓞_F` が **lying-over により全射**で、ゆえに切断を持つこと、

として `sorry` 無しに証明する。これは `InitialThetaData.Deferred.HasValuationSection` を将来
具体化するための Mathlib 前提(Track A)である。
-/

namespace IUT.NumberTheory

open Function

/-! ## 抽象: 付値の切断原理 -/

/-- **付値の切断** ([IUT-I] Def 3.1(e)): 素点の制限 `π : V_K → V_mod` の右逆 `s`。
`V ⊆ V(K)` を「`s` の像」としてモデル化する。 -/
def IsValuationSection {VK Vmod : Type*} (π : VK → Vmod) (s : Vmod → VK) : Prop :=
  RightInverse s π

/-- **(e) の核 1**: 全射 `V(K) ↠ V_mod` には必ず切断が存在する。 -/
theorem exists_valuationSection {VK Vmod : Type*} {π : VK → Vmod}
    (hπ : Surjective π) : ∃ s : Vmod → VK, IsValuationSection π s :=
  hπ.hasRightInverse

/-- **(e) の核 2**: 切断は単射、すなわち `V ≅ V_mod`(`V := s '' V_mod` は `V_mod` と全単射)。 -/
theorem IsValuationSection.injective {VK Vmod : Type*} {π : VK → Vmod} {s : Vmod → VK}
    (h : IsValuationSection π s) : Injective s :=
  Function.RightInverse.injective h

/-- 切断の像と `V_mod` の間の全単射 `V ≅ V_mod`。 -/
noncomputable def IsValuationSection.equivRange {VK Vmod : Type*} {π : VK → Vmod}
    {s : Vmod → VK} (h : IsValuationSection π s) : Vmod ≃ Set.range s :=
  Equiv.ofInjective s h.injective

/-! ## 整拡大への適用: lying-over が切断を与える -/

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- **整拡大の素点制限は全射**(lying-over / going-up)。整な単射拡大 `R → S` に対し、素スペクトルの
制限 `comap : Spec S → Spec R` は全射。数体 `K/F` の `𝓞_F → 𝓞_K` がこの場合であり、
これが `V(K) ↠ V_mod`(Def 3.1(e))の全射性を与える。 -/
theorem primeRestriction_surjective
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
  Algebra.IsIntegral.comap_surjective R S

/-- **整拡大には付値の切断が存在する**(Def 3.1(e) の具体化)。
すなわち各 `Spec R` の素点に、その上の `Spec S` の素点を選ぶ切断が取れる。 -/
theorem exists_valuationSection_of_isIntegral
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ∃ s : PrimeSpectrum R → PrimeSpectrum S,
      IsValuationSection (PrimeSpectrum.comap (algebraMap R S)) s :=
  exists_valuationSection (primeRestriction_surjective R S)

/-! ## 数体版 (M2): `Def 3.1(e)` の数学的内容そのもの -/

section NumberField

open scoped NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- 数体の整数環拡大 `𝓞_K → 𝓞_L` は**忠実**(`algebraMap` 単射、核 = ⊥)。 -/
instance instFaithfulSMul_ringOfIntegers : FaithfulSMul (𝓞 K) (𝓞 L) :=
  (faithfulSMul_iff_algebraMap_injective (𝓞 K) (𝓞 L)).mpr
    ((RingHom.injective_iff_ker_eq_bot _).mpr
      (NumberField.RingOfIntegers.ker_algebraMap_eq_bot K L))

/-- **数体の素点制限は全射** (lying-over): `V(L) ↠ V(K)`(`L/K` 数体拡大)。
整数環拡大 `𝓞_K → 𝓞_L` が整(`extension_algebra_isIntegral`)かつ忠実だから。 -/
theorem numberField_primeRestriction_surjective :
    Surjective (PrimeSpectrum.comap (algebraMap (𝓞 K) (𝓞 L))) :=
  primeRestriction_surjective (𝓞 K) (𝓞 L)

/-- **[IUT-I] Def 3.1(e) の数体版(M2)**: 数体拡大 `L/K`(IUT では `K/F_mod`)に対し、
素点制限 `V(L) ↠ V(K)` は切断を持ち、`V ≅ V(K)` なる `V ⊆ V(L)` が存在する。

これが条件 (e) の**数学的内容そのもの**であり、`l`-等分の体 `K` が(その出自に依らず)数体で
ある限り (e) が成立することを `sorry` 無しに示す。`HasValuationSection` を具体化する際は、
この定理を `L := K(E[l])`, `K := F_mod` に適用すればよい。 -/
theorem numberField_exists_valuationSection :
    ∃ s : PrimeSpectrum (𝓞 K) → PrimeSpectrum (𝓞 L),
      IsValuationSection (PrimeSpectrum.comap (algebraMap (𝓞 K) (𝓞 L))) s :=
  exists_valuationSection_of_isIntegral (𝓞 K) (𝓞 L)

end NumberField

open scoped NumberField in
/-- **[IUT-I] Def 3.1(e) の述語(具体版)**: 数体拡大 `K/Fmod` に対し、素点制限
`V(K) ↠ V(Fmod)` が切断を持つこと。これが初期 Θ データ条件 (e) の内容そのもの。
旧 `opaque IUT.HasValuationSection` を置き換える具体的な命題。 -/
def HasValuationSection (Fmod K : Type*) [Field Fmod] [Field K] [Algebra Fmod K] : Prop :=
  ∃ s : PrimeSpectrum (𝓞 Fmod) → PrimeSpectrum (𝓞 K),
    IsValuationSection (PrimeSpectrum.comap (algebraMap (𝓞 Fmod) (𝓞 K))) s

/-- **条件 (e) は数体拡大に対し常に成立する**(M2.5): lying-over により素点制限が全射ゆえ
切断が存在する。これにより Def 3.1(e) は IUT の独立した*仮定*ではなく**証明される定理**となる。 -/
theorem hasValuationSection (Fmod K : Type*) [Field Fmod] [Field K] [Algebra Fmod K] :
    HasValuationSection Fmod K :=
  numberField_exists_valuationSection Fmod K

end IUT.NumberTheory
