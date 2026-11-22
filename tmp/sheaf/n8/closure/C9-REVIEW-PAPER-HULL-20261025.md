# C9 review：paper Cor3.12 的 hull/finiteness 论证

任务：task-426（Review hull/finiteness in paper proof）。owner：iplsheapt。日期：2026-10-25。只做 accept/reject；不改 Lean/Project/目标；只写本文件。No mixed/E3。

被审对象：C9-COR312-PAPER-PROOF-20261025.md（100 lines，SHA256 91F6BD347D7BABA6854BCE81ED185A553F536D27615EA4356D2F50F0B818431B）§2（hull/finiteness）。源：IUT III lines 10220-10240（compactness of `1,circ U_{j,vQ}`, log-volume finiteness）。

## 0. Verdict

**REJECT Section2 的 hull/finiteness 论证为 sufficient paper-level proof；可接受条件只是引用 source 的 compactness/log-volume finiteness，而不是 Section2 给出的“finite index ⇒ H compact”论证。**

Section2 的具体错误在：

```
(R1) “for fixed C the index set is finite” 没有 source proof；j∈F_l^* 有限，但 vQ∈VQ 是 Q 的 valuations，一般不有限。
(R2) 每个 1,circ U_{j,vQ} compact 不推出 union/hull H compact；需要相对紧/hull 的额外证明。
(R3) 从 H compact 到 h=−|logΘ| finite 还需要 Prop3.9 的 log-volume 定义/收敛；Section2 只引用，未证明。
```

Source 本身（IUT III 10234-10237）说的是：由 `1,circ U_{j,vQ}` 的 compactness + log-volume 定义，`−|logΘ|` finite；它没有说 index set finite，也没有说 H compact。Section2 把 source 的 compactness 解释成 Section2 自己的 finite-index argument，逻辑不成立。

## 1. Step-by-step accept/reject

| step | claim | verdict | reason |
|---|---|---|---|
| S1 | H = holomorphic hull of PI in `1,circ U`; smallest `λ*O` region. | **ACCEPT definitional/source** | Rem3.9.5(i) defines hull as smallest λO region; PI union of possible images. Caveat IQ(-)/+∞ not discussed in Section2. |
| S2 | Each `1,circ U_{j,vQ}` is compact (source 10234-10237). | **ACCEPT as source-asserted** | Source says easily verified compactness; Section2 does not prove it, but citation is accurate. |
| S3 | For fixed C the index set `j∈F_l^*, vQ∈VQ` is finite. | **REJECT** | `j` finite, but VQ is a set of valuations of Q; no source theorem makes it finite. IUT III products/sums over vQ∈VQ; the log-volume uses normalization/product formula, not finite index. |
| S4 | Finite union of compact `1,circ U_{j,vQ}` ⇒ H compact. | **REJECT** | (a) S3 false; (b) even finite union of compact containers does not imply the **hull** H is compact; hull can be larger/whole IQ. Source does not assert H compact. |
| S5 | H compact and Prop3.9 ⇒ h finite. | **CONDITIONAL/REJECT as derived** | If H compact and log-volume finite on compact sets, h finite; but H compact is unproved. Source instead directly asserts finiteness from compactness of `1,circ U_{j,vQ}` + log-volume; that source argument is not the Section2 argument. |
| S6 | `R_{≤h}` definition; outputs have log-volumes ≤h. | **ACCEPT definitional** | Once h finite; no numeric equality. |

## 2. Why finite index is suspect

In IUT III, `VQ` denotes the set of valuations of Q. For F_mod=Q, VQ includes all rational primes and the archimedean valuation; it is **infinite**. The source's tensor packet/product is over `vQ∈VQ`. The compactness statement is for each `1,circ U_{j,vQ}`; the finiteness of `−|logΘ|` comes from the definition/normalization of log-volume and compactness, not from a finite index set. Section2's phrase “for fixed C the index set is finite” is an unproved reinterpretation; at face value it is false for VQ.

Even if one restricts to the finite set of **bad** places V_bad, the multiradial representation `1,circ U` is indexed by all `vQ∈VQ`; good/arch places contribute (possibly zero/normalized) terms. Section2 does not state a finite subset; it says index set finite without proof.

## 3. Hull compactness is not automatic

The hull is the smallest `λ*O` region containing PI. A union of compact subsets of a locally compact space need not be relatively compact if the index set is infinite; and the holomorphic hull of a compact set need not be compact without a boundedness/relative compactness hypothesis. Source's compactness of individual `1,circ U_{j,vQ}` does not by itself establish H compact. If H is the whole `I_Q`, `h=+∞`, and the inequality is not finite. Section2's S4 leap is the exact gap.

## 4. What the source actually supports

IUT III lines 10234-10237:

```
one concludes easily from the [easily verified] compactness of the 1,circ U_{j,vQ}
[j∈|Fl|, vQ∈VQ], together with the definition of the log-volume, that
−|log Θ| is finite.
```

This is a **source assertion** relying on the log-volume definition, not the Section2 finite-index/H-compact argument. It may be accepted at paper level as the source's compactness input, but Section2's explanation is not equivalent and not a proof.

## 5. Verdict on paper-level sufficiency

If “paper-level” means “cite IUT III's compactness/log-volume finiteness step,” then the **source theorem** can be accepted at paper level. But the specific Section2 argument is **insufficient/incorrect**: finite index is unproved/possibly false, and H compact does not follow. The exact missing steps are:

```
(F1) a precise finite/relevant index set for vQ or a proof that the infinite product/sum
     is compatible with log-volume finiteness;
(F2) relative compactness/compactness of H (or a direct source finiteness proof);
(F3) the Prop3.9 log-volume finiteness theorem on the relevant class.
```

None is supplied by Section2's two sentences.

## 6. Classification

| item | status |
|---|---|
| H definition / λO hull | ACCEPT source/definition |
| compactness of each 1,circ U_{j,vQ} | ACCEPT source-asserted |
| finite index j,vQ | **REJECT** (unproved; VQ infinite generally) |
| finite union ⇒ H compact | **REJECT** |
| H compact ⇒ h finite | CONDITIONAL |
| source finiteness by compactness+logvolume | ACCEPT as paper citation |
| Section2 argument sufficient | **REJECT** |
| Cor3.12 paper theorem | ACCEPT via source citation, not Section2 proof |
| P6_can via this proof | NOT established by Section2 |

## 7. Conclusion

Section2's hull/finiteness explanation is rejected: it asserts a finite index set for `j∈F_l^*, vQ∈VQ` without proof (and VQ is generally infinite), then infers H compact from compact containers and finite union. Neither implication is valid. The source does assert finiteness from compactness of each `1,circ U_{j,vQ}` plus the log-volume definition; that source assertion can be cited at paper level, but Section2's derivation is not a proof. Exact gaps F1-F3 remain. No Lean/mixed/E3; P6 open.

