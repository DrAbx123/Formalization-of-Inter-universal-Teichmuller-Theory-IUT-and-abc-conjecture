import Mathlib
import tmp.sheaf.takkun.IutLean.Combinatorics.Fl

/-!
# 組合せ的 Teichmüller 理論: 2 つの対称性の単純推移性

底本: [IUT-I] §4 (Multiplicative Combinatorial Teichmüller Theory),
§6 (Additive Combinatorial Teichmüller Theory), 星裕一郎入門 §18, §20, §21。

Hodge 劇場は 2 種類の対称性のもとで構成される:

* **加法的/幾何学的対称性** `F_l^{⋊±} = F_l ⋊ {±1}` ―― 加法的ラベル `LabCusp± ≅ F_l` に作用。
  その並進部分 `F_l` は `LabCusp±` に**単純推移的**に作用する。
* **乗法的/数論的対称性** `F_l^⋆ = F_l^×/{±1} = LabCusp` ―― 乗法的ラベル `LabCusp` に作用。
  群が自身に左並進で作用するので、これも**単純推移的**。

この「ラベルの単純推移的な管理」が組合せ的 Teichmüller 理論の核心であり、本ファイルで
`sorry` 無しに証明する。Phase 1 (`Fl`, `LabCusp`) に直接接続する。
-/

namespace IUT.HodgeTheater

open IUT

/-! ## 加法的(幾何学的)組合せ Teichmüller 理論 ([IUT-I] §6) -/

/-- **加法的対称性の単純推移性**: 加法的ラベル `LabCusp± ≅ F_l` の任意の 2 元 `j, j'` に対し、
`a + j = j'` を満たす並進 `a ∈ F_l` がただ 1 つ存在する。`F_l^{⋊±}` の並進部分 `F_l` は
`LabCusp±` に単純推移的に作用する。 -/
theorem additive_simplyTransitive (l : ℕ) (j j' : Fl l) :
    ∃! a : Fl l, a + j = j' :=
  ⟨j' - j, by ring, fun a ha => by rw [← ha]; ring⟩

/-! ## 乗法的(数論的)組合せ Teichmüller 理論 ([IUT-I] §4) -/

/-- 群はその左並進作用によって自身に単純推移的に作用する。 -/
theorem group_simplyTransitive {Q : Type*} [Group Q] (j j' : Q) :
    ∃! a : Q, a * j = j' :=
  ⟨j' * j⁻¹, by group, fun a ha => by rw [← ha]; group⟩

/-- **乗法的対称性の単純推移性**: 乗法的ラベル `LabCusp = F_l^×/{±1}` の任意の 2 元に対し、
それらを移す対称性 `F_l^⋆` の元がただ 1 つ存在する(`F_l^⋆ = LabCusp` の左並進作用)。 -/
theorem multiplicative_simplyTransitive (l : ℕ) [Fact l.Prime]
    (j j' : LabCusp l) : ∃! a : LabCusp l, a * j = j' :=
  group_simplyTransitive j j'

end IUT.HodgeTheater
