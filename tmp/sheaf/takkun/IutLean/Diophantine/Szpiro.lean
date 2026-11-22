import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.MainTheorem

/-!
# Diophantus 的帰結: Szpiro 不等式 / 楕円曲線版 ABC

底本: 星裕一郎『宇宙際 Teichmüller 理論入門』§4 冒頭, §12 / [IUT-IV] §1, §2。

主定理(多輻的表示, Phase 8 `MultiradialRepresentation`)
  `|deg(q 標対象)| ≥ -vol((Ind1,2,3)-orbit of Θ 標対象 の正則包)`
と、Θ 標対象の次数を支配する Gauss 和(Phase 8 `twentyFour_mul_thetaPilotDegree`: `24θ = l³−l`)、
及び [IUT-IV] §1, §2 の対数体積計算(素数 `l` の適切な選択を含む「初等的計算」)を併せると、
楕円曲線の高さ(= q 標対象の次数)に対する評価 ―― **Szpiro 不等式 / 楕円曲線版 ABC 不等式** ――
が得られる。

ここでは楕円曲線の数論的不変量を実数として束ね、最終的な不等式を**明示的な形**で述べる。
不等式の*成立*そのものは IUT 全体＋[IUT-IV] の対数体積計算の帰結ゆえ `DiophantineMainTheorem`
として保留するが、その**主張**と、それを支える初等的実数算術は明示・証明する。
-/

namespace IUT.Diophantine

open IUT.Multiradial

/-- 初期 Θ データの楕円曲線に付随する(対数的)数論的不変量(実数):
高さ `htLog`(≈ q 標対象の次数 `|deg(q)|`)、log-conductor `condLog`、log-different `diffLog`。 -/
structure EllipticInvariants where
  /-- 対数的高さ `≈ |deg(q 標対象)|`。 -/
  htLog : ℝ
  /-- log-conductor。 -/
  condLog : ℝ
  /-- log-different。 -/
  diffLog : ℝ
  htLog_nonneg : 0 ≤ htLog
  condLog_nonneg : 0 ≤ condLog
  diffLog_nonneg : 0 ≤ diffLog

/-- **Szpiro / ABC 不等式の主張**(誤差 `ε`, 定数 `C`):
`htLog ≤ (1 + ε) · (diffLog + condLog) + C`。
[IUT-IV] の主定理が任意の `ε > 0` に対して(`ε` に依存する `C` とともに)成立を主張する不等式。 -/
def SzpiroStatement (E : EllipticInvariants) (ε C : ℝ) : Prop :=
  E.htLog ≤ (1 + ε) * (E.diffLog + E.condLog) + C

/-- 不等式は定数 `C` について単調(弱められる): より大きい `C'` でも成立する。 -/
theorem SzpiroStatement.weaken {E : EllipticInvariants} {ε C C' : ℝ}
    (h : SzpiroStatement E ε C) (hC : C ≤ C') : SzpiroStatement E ε C' := by
  unfold SzpiroStatement at *; linarith

/-- 誤差項 `ε ≥ 0` のもとでは、`ε` を大きくしても成立は保たれる(`diffLog, condLog ≥ 0` ゆえ)。 -/
theorem SzpiroStatement.weaken_eps {E : EllipticInvariants} {ε ε' C : ℝ}
    (h : SzpiroStatement E ε C) (hε : ε ≤ ε') (_hε0 : 0 ≤ ε) :
    SzpiroStatement E ε' C := by
  unfold SzpiroStatement at *
  have hD : 0 ≤ E.diffLog + E.condLog := by
    have := E.diffLog_nonneg; have := E.condLog_nonneg; linarith
  nlinarith [h, mul_le_mul_of_nonneg_right (sub_nonneg.mpr hε) hD]

/-- **ABC 形への変形**(初等的算術): Szpiro 形 `htLog ≤ (1+ε)(diffLog+condLog)+C` は、
`htLog − (1+ε)·condLog ≤ (1+ε)·diffLog + C` と同値。[IUT-IV] §1,§2 の「初等的計算」の一例。 -/
theorem szpiro_iff_abc (E : EllipticInvariants) (ε C : ℝ) :
    SzpiroStatement E ε C ↔
      E.htLog - (1 + ε) * E.condLog ≤ (1 + ε) * E.diffLog + C := by
  unfold SzpiroStatement
  constructor <;> intro h <;> nlinarith [h]

/-- **IUT の Diophantus 的主定理の主張**([IUT-IV] Thm 1.10 / Cor 2.2):
任意の `ε > 0` に対し、ある定数 `C` が存在して Szpiro 不等式 `SzpiroStatement E ε C` が成立する。

旧 `opaque` を**具体的な命題**に置き換え、主張を明示した(もはやブラックボックスではない)。
この命題の*成立そのもの*は Phase 8 の主不等式と Gauss 和(`24θ = l³−l`)、及び [IUT-IV] の
対数体積計算の帰結であり、IUT 全体を要する深い定理ゆえ、ここでは*主張の明示*に留める
(`sorry`/`axiom` で証明したと偽らない)。 -/
def DiophantineMainTheorem (E : EllipticInvariants) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, SzpiroStatement E ε C

end IUT.Diophantine
