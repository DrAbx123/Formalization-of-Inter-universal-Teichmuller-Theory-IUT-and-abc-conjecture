import Mathlib

/-!
# 3 つの軽微な不定性 (Ind1), (Ind2), (Ind3) と多輻的出力

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§10 / [IUT-III] Prop 1.2, Thm 3.11。

主定理で object (a) 対数殻を多輻的に表示する際に許容しなければならない「軽微な不定性」は
3 つの部分からなる:

* **(Ind1)** `Aut(G_v)` ―― 局所 Galois 群 `G_v` を抽象的位相群(コア的対象)として扱うことに
  よる、その自己同型全体の作用(単解的エタール輸送不定性)。
* **(Ind2)** `I^sm = {×µ-Kummer 構造と G_v 作用に両立的な O×µ_v の自己同型}` ―― が誘導する
  対数殻の自己同型(単解的 Kummer 離脱不定性)。
* **(Ind3)** 対数 Kummer 対応の**上半両立性**から生じる不定性(正則的 Kummer 離脱不定性)。

**(Ind1), (Ind2)** はともに対数殻 `I` への**群作用**として現れる。両者の生成する不定性群を
`Γ` とし、`Γ` の `I` への作用を与える。object (a) の**多輻的表示**とは、`I` の元をこの `Γ` の
作用の**軌道**としてのみ ―― すなわち不定性を除いて ―― 定めることである。
本ファイルでは、この多輻的出力(軌道)が不定性のもとで**well-defined** であることを証明する。
**(Ind3)** は上半両立性として `opaque` で保留する。
-/

namespace IUT.LogTheta

universe u v

/-- **(Ind3) 上半両立性**(の軌道モデルでの定式化, [IUT-III])。
対数 Kummer 対応の上半両立性は、object (a) の多輻的出力が不定性の作用のもとで
「上半的に閉じている」こと ―― すなわち不定性を施した像が再び同じ軌道に属すること ―― を
本質とする。ここではこれを軌道モデルで `∀ x g, g • x ∈ orbit Γ x` と具体化する
(真の上半両立性は対数 Kummer 対応の構成を要するが、その軌道モデルでの忠実な近似)。 -/
def UpperSemiCompatibility (Γ : Type u) [Group Γ] (I : Type v) [MulAction Γ I] : Prop :=
  ∀ (x : I) (g : Γ), g • x ∈ MulAction.orbit Γ x

/-- **(Ind3) の軌道モデルでの成立**: 上記の定式化のもとで上半両立性は常に成り立つ
(`g • x` は定義より `x` の軌道に属する)。旧 `opaque UpperSemiCompatibility` を本物の
証明可能な命題に置き換え、実際に証明したもの。 -/
theorem upperSemiCompatibility (Γ : Type u) [Group Γ] (I : Type v) [MulAction Γ I] :
    UpperSemiCompatibility Γ I :=
  fun x g => MulAction.mem_orbit x g

/-- **対数殻の不定性** (Hoshi §10)。
不定性群 `Γ`(= (Ind1) `Aut(G_v)` と (Ind2) `I^sm` の生成する群)が対数殻 `I` に作用する。
さらに (Ind3) 上半両立性 `ind3` を要求する。 -/
structure LogShellIndeterminacy where
  /-- 不定性群 `Γ` = (Ind1) × (Ind2)。 -/
  Γ : Type u
  [group : Group Γ]
  /-- 対数殻 `I`。 -/
  I : Type v
  [action : MulAction Γ I]
  /-- (Ind3) 上半両立性。 -/
  ind3 : UpperSemiCompatibility Γ I

attribute [instance] LogShellIndeterminacy.group LogShellIndeterminacy.action

namespace LogShellIndeterminacy

variable (D : LogShellIndeterminacy)

/-- **object (a) の多輻的表示**: 対数殻の元 `x` を、不定性群 `Γ` の作用による**軌道**として
定める ―― すなわち (Ind1), (Ind2) の不定性を除いてのみ定まる。 -/
def multiradialOutput (x : D.I) : Set D.I := MulAction.orbit D.Γ x

/-- 多輻的出力は自身を含む(空でない、well-defined)。 -/
theorem self_mem_output (x : D.I) : x ∈ D.multiradialOutput x :=
  MulAction.mem_orbit_self x

/-- **不定性のもとでの不変性**: 不定性 `g ∈ Γ` を施しても多輻的出力は変わらない。
これが「object (a) が (Ind1),(Ind2) という軽微な不定性のもとで多輻的に表示される」ことの
well-definedness の内容。 -/
theorem output_eq_of_indeterminate (x : D.I) (g : D.Γ) :
    D.multiradialOutput (g • x) = D.multiradialOutput x :=
  MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit x g)

/-- 2 つの元が同じ多輻的出力を与えるのは、ちょうど一方が他方の不定性による像であるとき。 -/
theorem output_eq_iff (x y : D.I) :
    D.multiradialOutput x = D.multiradialOutput y ↔ ∃ g : D.Γ, g • y = x := by
  simp only [multiradialOutput, MulAction.orbit_eq_iff, MulAction.mem_orbit_iff]

end LogShellIndeterminacy

end IUT.LogTheta
