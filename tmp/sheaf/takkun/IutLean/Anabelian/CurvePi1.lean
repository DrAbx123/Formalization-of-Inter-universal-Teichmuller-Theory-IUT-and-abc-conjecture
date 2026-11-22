import Mathlib
import tmp.sheaf.takkun.IutLean.Anabelian.Core

/-!
# 曲線のエタール基本群 π₁ — Galois 圏によるエタール π₁ の基盤

底本: SGA1 / Lenstra "Galois theory for schemes" / [IUT-I] §1–§2(算術的基本群 `Π_X`)。

双曲的曲線 `X` のエタール基本群 `π₁(X)` は、`X` の**有限エタール被覆の圏**(Galois 圏)の
ファイバー関手 `F` の自己同型群 `Aut F` として定義される。IUT の算術的基本群
`Π_X = π₁(X)`・幾何学的基本群 `Δ_X` はすべてこの形で生じる。

Mathlib には Galois 圏の公理的枠組み(`CategoryTheory.PreGaloisCategory` /
`FiberFunctor`、SGA1 (G1)–(G6))と、その基本定理(プロ表現可能性・`Aut F` のプロ有限性・
連結対象上の推移性・**有限連続 `π₁`-集合の圏との圏同値**)が完備されている。本モジュールは
これを IUT の言葉(`EtalePi1`)で橋渡しし、`IsKCore` 解消(`CoreData.lean`)へ向けた
**曲線 π₁ 基盤**の第一層とする:

* `EtalePi1 F := Aut F` ―― エタール基本群;
* **プロ有限性**(`etalePi1_compact`/`_t2`/`_totallyDisconnected`)―― `Π_X` がプロ有限位相群
  であること([IUT-I] で常時使用される基本事実);
* **ファイバーへの作用と連結対象上の推移性**(`etalePi1_pretransitive`)―― 被覆理論の核;
* **基本定理**(`etalePi1_equivalence`): 被覆圏 `C ≌ π₁ の有限連続作用の圏` ―― 遠アーベル
  幾何の出発点「被覆の圏 = π₁ の表現圏」。
-/

namespace IUT.Anabelian

open CategoryTheory PreGaloisCategory

universe u v w

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- **曲線のエタール基本群** `π₁(X) := Aut F`(有限エタール被覆の Galois 圏 `C` の
ファイバー関手 `F` の自己同型群)。IUT の `Π_X`/`Δ_X` はすべてこの形。 -/
abbrev EtalePi1 : Type _ := Aut F

/-- エタール基本群はコンパクト(プロ有限性の一部)。 -/
theorem etalePi1_compact : CompactSpace (EtalePi1 F) := inferInstance

/-- エタール基本群は Hausdorff(プロ有限性の一部)。 -/
theorem etalePi1_t2 : T2Space (EtalePi1 F) := inferInstance

/-- エタール基本群は完全不連結(プロ有限性の一部)。コンパクト + Hausdorff + 完全不連結
= **プロ有限** ―― `Π_X` がプロ有限位相群であること([IUT-I] の基本前提)。 -/
theorem etalePi1_totallyDisconnected : TotallyDisconnectedSpace (EtalePi1 F) :=
  inferInstance

/-- エタール基本群は位相群(乗法・逆元が連続)。 -/
theorem etalePi1_topologicalGroup : IsTopologicalGroup (EtalePi1 F) := inferInstance

/-- **連結被覆のファイバーへの π₁ 作用は推移的**(被覆理論の核、SGA1)。
`X_K → C_K` 型の連結被覆のファイバーを `Π` が推移的に動かすこと。 -/
theorem etalePi1_pretransitive (X : C) [IsConnected X] :
    MulAction.IsPretransitive (EtalePi1 F) (F.obj X) := inferInstance

/-- **Galois 圏の基本定理**(SGA1 / Lenstra): 有限エタール被覆の圏は、エタール基本群
`π₁ = Aut F` の**有限連続作用の圏と圏同値**。遠アーベル幾何の出発点
「被覆の圏 = `π₁` の表現圏」―― 群 `Π_X` から幾何(被覆)が完全に復元される。 -/
theorem etalePi1_equivalence : (functorToContAction F).IsEquivalence := inferInstance

/-- エタール基本群は `IsFundamentalGroup` の公理(連結対象上の推移性・Galois 対象での
非自明性・普遍性)を満たす。 -/
theorem etalePi1_isFundamentalGroup : IsFundamentalGroup F (EtalePi1 F) := inferInstance

end IUT.Anabelian
