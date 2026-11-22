/-
H-T §8.2: F_mod 在 ℚ 上的极大分歧指数 e_mod 及两条界。

* `ramificationIdxOverInt T P`: F_mod 整数环的素理想 P 在 ℤ 上的分歧指数
  （经 P.under ℤ 的整数生成元 `underIntGen P`；base 为 ℤ）；
* `eMod T`: 论文的 e_mod = max(1, sup_{P ∈ differentPlaces F_mod} e_P)。
  `differentPlaces F_mod` 是 differentIdeal ℤ 𝓞_{F_mod} 的素因子支撑；对 F_mod/ℚ，
  e_P > 1 ⟹ P ∣ different，故全体有限素理想上的极大分歧指数等于该 sup 与 1 的较大者
  （不同素理想都未分歧时 e_mod = 1）；
* `dModFmod T`: 论文的 d_mod = [F_mod : ℚ]（实数值）；
* `one_le_eMod`: 1 ≤ e_mod；
* `eMod_le_finrank` / `eMod_le_dMod`: e_mod ≤ [F_mod : ℚ]，实数形式 (e_mod : ℝ) ≤ d_mod。

donors（不重证）:
* `differentPlaces`（Mzk1HT82AbsDifferentSumActual）及其 normalizedFactors 成员性；
* `underIntGen`、`underIntGen_liesOver`（Mzk1HT82UnderIntGenQVActual /
  Mzk1HT82PaperWeightDiffActual）；
* Mathlib `Ideal.ramificationIdx_le_finrank`（NumberTheory/RamificationInertia/Basic：
  p.ramificationIdx' P ≤ [Frac S : Frac R]）、`Ideal.IsPrime.isMaximal`、
  `Ideal.under_ne_bot`。 -/
import Mathlib.Tactic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.Basic
import tmp.sheaf.xif.paper.Mzk1HT82AbsDifferentSumActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULEModActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open NumberField UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

universe u

variable {l : PrimeGeFive}

/-! ## 定义 -/

/-- F_mod 整数环的素理想 P 在 ℤ 上的分歧指数（沿 P.under ℤ 的整数生成元）。

等价地 `ramificationIdx' (span {underIntGen P}) P`：Mathlib 的 ramificationIdx'
取使 `map (algebraMap ℤ (𝓞 F_mod)) (span {underIntGen P}) ≤ P ^ n` 的最大 n。
P 非素时取 junk 值 0；本文件只在 `differentPlaces F_mod`（均为素理想）上使用。 -/
noncomputable def ramificationIdxOverInt (T : SourceNativeInitialThetaData.{0} l)
    (P : Ideal (𝓞 T.arithmetic.Fmod)) : ℕ :=
  Ideal.ramificationIdx' (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}) P

/-- **论文的 e_mod**: F_mod 在 ℚ 上的极大分歧指数。

differentPlaces F_mod 上的分歧指数 sup 与 1 的较大者。 -/
noncomputable def eMod (T : SourceNativeInitialThetaData.{0} l) : ℕ :=
  (differentPlaces T.arithmetic.Fmod).sup (ramificationIdxOverInt T) ⊔ 1

/-- **论文的 d_mod** = [F_mod : ℚ]（实数值）。 -/
noncomputable def dModFmod (T : SourceNativeInitialThetaData.{0} l) : ℝ :=
  (Module.finrank ℚ T.arithmetic.Fmod : ℝ)

/-! ## differentPlaces 的成员是素理想 -/

/-- differentPlaces F_mod 的成员都是素理想（normalizedFactors 的不可约因子）。 -/
theorem isPrime_of_mem_differentPlaces
    (T : SourceNativeInitialThetaData.{0} l) {P : Ideal (𝓞 T.arithmetic.Fmod)}
    (hP : P ∈ differentPlaces T.arithmetic.Fmod) : P.IsPrime := by
  classical
  have hI : differentIdeal ℤ (𝓞 T.arithmetic.Fmod) ≠ ⊥ := differentIdeal_ne_bot
  exact ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp hP)).1

/-- differentPlaces F_mod 的成员非零（differentIdeal ≠ ⊥）。 -/
theorem ne_bot_of_mem_differentPlaces
    (T : SourceNativeInitialThetaData.{0} l) {P : Ideal (𝓞 T.arithmetic.Fmod)}
    (hP : P ∈ differentPlaces T.arithmetic.Fmod) : P ≠ ⊥ := by
  classical
  have hI : differentIdeal ℤ (𝓞 T.arithmetic.Fmod) ≠ ⊥ := differentIdeal_ne_bot
  have hle : differentIdeal ℤ (𝓞 T.arithmetic.Fmod) ≤ P :=
    ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp hP)).2
  rintro rfl
  exact hI (le_bot_iff.mp hle)

/-! ## 每个分歧指数 ≤ [F_mod : ℚ] -/

/-- P ∈ differentPlaces F_mod 时，P 在 ℤ 上的分歧指数 ≤ [F_mod : ℚ]
（Mathlib 的 `Ideal.ramificationIdx_le_finrank`，取 p = span {underIntGen P} 极大）。 -/
theorem ramificationIdxOverInt_le_finrank
    (T : SourceNativeInitialThetaData.{0} l) {P : Ideal (𝓞 T.arithmetic.Fmod)}
    (hP : P ∈ differentPlaces T.arithmetic.Fmod) :
    ramificationIdxOverInt T P ≤ Module.finrank ℚ T.arithmetic.Fmod := by
  classical
  have hI : differentIdeal ℤ (𝓞 T.arithmetic.Fmod) ≠ ⊥ := differentIdeal_ne_bot
  have hmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 T.arithmetic.Fmod)) :=
    Multiset.mem_toFinset.mp hP
  obtain ⟨hprime, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hmem
  have hPne : P ≠ ⊥ := by
    rintro rfl
    exact hI (le_bot_iff.mp hle)
  haveI : P.IsPrime := hprime
  have hlies : P.LiesOver (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}) :=
    underIntGen_liesOver (K := T.arithmetic.Fmod) P
  haveI : P.LiesOver (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}) := hlies
  have hspan : Ideal.span {underIntGen (K := T.arithmetic.Fmod) P} = P.under ℤ := hlies.over
  have hunderNe : P.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ hPne
  have hpne : Ideal.span {underIntGen (K := T.arithmetic.Fmod) P} ≠ ⊥ := by
    rw [hspan]
    exact hunderNe
  have hpprime : (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}).IsPrime := by
    rw [hspan]
    exact inferInstance
  haveI : (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}).IsPrime := hpprime
  haveI : (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}).IsMaximal :=
    Ideal.IsPrime.isMaximal hpprime hpne
  change Ideal.ramificationIdx' (Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}) P
      ≤ Module.finrank ℚ T.arithmetic.Fmod
  exact Ideal.ramificationIdx_le_finrank (R := ℤ)
    (S := NumberField.RingOfIntegers (T.arithmetic.Fmod))
    (K := ℚ) (L := T.arithmetic.Fmod)
    (p := Ideal.span {underIntGen (K := T.arithmetic.Fmod) P}) (P := P)

/-! ## 两条界 -/

/-- **1 ≤ e_mod**：分歧指数均 ≥ 1（未分歧时为 1）。 -/
theorem one_le_eMod (T : SourceNativeInitialThetaData.{0} l) : 1 ≤ eMod T := by
  unfold eMod
  exact le_sup_right

/-- **e_mod ≤ [F_mod : ℚ]**（自然数形式）。 -/
theorem eMod_le_finrank (T : SourceNativeInitialThetaData.{0} l) :
    eMod T ≤ Module.finrank ℚ T.arithmetic.Fmod := by
  classical
  have h1 : (1 : ℕ) ≤ Module.finrank ℚ T.arithmetic.Fmod :=
    Module.finrank_pos (R := ℚ) (M := T.arithmetic.Fmod)
  unfold eMod
  exact sup_le (Finset.sup_le fun P hP => ramificationIdxOverInt_le_finrank T hP) h1

/-- **e_mod ≤ d_mod**（实数形式 (e_mod : ℝ) ≤ [F_mod : ℚ]）。 -/
theorem eMod_le_dMod (T : SourceNativeInitialThetaData.{0} l) :
    (eMod T : ℝ) ≤ dModFmod T := by
  rw [dModFmod]
  exact_mod_cast eMod_le_finrank T

/-- d_mod > 0（F_mod 是数域，[F_mod : ℚ] ≥ 1）。 -/
theorem dModFmod_pos (T : SourceNativeInitialThetaData.{0} l) : 0 < dModFmod T := by
  rw [dModFmod]
  have h : 0 < Module.finrank ℚ T.arithmetic.Fmod :=
    Module.finrank_pos (R := ℚ) (M := T.arithmetic.Fmod)
  exact_mod_cast h

#check @ramificationIdxOverInt
#check @eMod
#check @dModFmod
#print axioms one_le_eMod
#print axioms eMod_le_finrank
#print axioms eMod_le_dMod
#print axioms dModFmod_pos
#print axioms ramificationIdxOverInt_le_finrank

end LeanFormal.IUT.XiFPaper.Mzk1ULEModActual
