# C9 C1 domain-corrected output bridge（D4）

任务：task-454（Corrected route output bridge）。owner：iplsheapt。日期：2026-10-25。Audit D4；不改 Lean/Project/目标；只写本文件。No mixed/E3。

输入：C9-C1-DOMAIN-CORRECTION-20261025.md；C9-C1-VOL-BRIDGE-20261025.md；C9-C1-LS-BRIDGE-20261025.md；LANA §9.2；IUT III Step(xi-e)-(xi-f)。

## 0. Verdict

**D4 不成立：`eta_q=eta^anab_S`（S∈VC(I)，`[1*S]=[S_q]`）不蕴含存在 actual output `D0∈O` with `logVol(D0)=Q`。** Domain correction 修好了容器 type mismatch，但没有修 output bridge：eta equality 给的是 **Rss 的 volume class** `[1*S]=[S_q]`，不是 multiradial output set O 的元素；`S_q` 本身是 q-pilot **input/target pilot**，不是 output。

## 1. D4 assumptions

```
S ∈ VC(I) (large container),  T_1(S)=1*S (LGP action),  [T_1(S)]=[S_q] in Rss;
eta_q = eta^anab_S : R^val → R^ss.
```

D4 claims: there exists `D0∈O` (multiradial possible output modulo Ind1/2/3) with `logVol(D0)=Q`, where `Q=-|log q|`.

## 2. What eta equality gives

By Lemma A/pointed linear equality,

```
eta_q=eta^anab_S ⇒ [T_1(S)]=[S_q] in R^ss
⇒ vol(T_1(S))=vol(S_q)=Q.
```

This is a volume-class equality in `R^ss = {T⊂VC(I)|adelic measurable}/~`. It gives a region `T_1(S)` (or its class) with volume Q, but does not say `T_1(S)∈O`.

## 3. Why O is not reached

1. `O` is the set of possible output data/regions of the Theorem3.11 multiradial algorithm, subject to Ind1/2/3. `VC(I)`/`Rss` is the ambient volume container/quotient. No inclusion `Rss ⊂ O` or `O = Rss` is asserted.

2. `S` is an admissible integral structure/input for the eta algorithm; `T_1(S)=1*S` is its LGP translate. The LGP/N-action is not stated to preserve the multiradial output set O; O is not closed under `T_1`.

3. `S_q={q_vO_v}` is the q-pilot **target pilot**, i.e. input-side datum. It is not an output element of O. Even the stronger exact equality `T_1(S)=S_q` would only produce the q-pilot region, not an output `D0`.

4. `[T_1(S)]=[S_q]` is a quotient class: it may hold by volume alone, with `T_1(S)` any adelic measurable region of volume Q, not necessarily an output. The quotient forgets set-theoretic membership.

Thus D4 has no implication. The premise is compatible with O containing only outputs of other log-volumes; no contradiction.

## 4. Counterexample schema to D4

Take a model where:

```
- Rss contains the class [S_q] of volume Q (so eta equality can hold for suitable S);
- O is a subset of possible outputs whose log-volumes are all ≠Q, e.g. a singleton
  output of volume Q'≠Q, or a set of outputs avoiding Q.
```

Then `eta_q=eta^anab_S` and `[1*S]=[S_q]` hold, but no `D0∈O` has logVol Q. Nothing in A1/A2/A3 or the domain correction forbids this model: O is not defined as all volume-Q regions. This is a logical counterexample schema, not an actual admissible C; it shows D4 is not a formal consequence. The source's xi-f is intended to rule it out, but that is exactly the missing compatibility C1, not a premise.

## 5. Conditional theorem / exact obstruction

**Theorem 5.1.** If eta equality and `[1*S]=[S_q]` hold, and additionally there exists `D0∈O` with `logVol(D0)=Q`, then C1 holds. The extra hypothesis is exactly the missing membership.

More precisely, D4 would follow from one of:

```
(D4-a) T_1(S) ∈ O and logVol(T_1(S))=Q;
(D4-b) a representative of the Rss class [S_q] lies in O;
(D4-c) an exact xi-f theorem: Q is the log-volume of an actual output D0.
```

None follows from `S∈VC(I)`, `[1*S]=[S_q]`, or eta equality. (D4-c) is the source compatibility/xi-f step; using it is circular.

## 6. Relation to xi-e/f

xi-e says the output construction is expressible under the condition that the pilot log-volume equals Q; xi-f says the construction of output possibilities “constitutes” Q, perhaps only up to approximation, and the inclusion follows formally. This is a statement about the construction/image, not a consequence of a volume class in Rss. Applying xi-f to D4 is using C1 to prove C1. The domain correction does not change this.

## 7. Classification

| item | status |
|---|---|
| S∈VC(I), T_1(S)=1*S | ACCEPT domain correction |
| eta equality ⇒ [1*S]=[S_q] in Rss | ACCEPT conditional |
| eta equality ⇒ T_1(S)∈O | **REJECT** |
| eta equality ⇒ ∃D0∈O with logVol Q | **REJECT (D4 false)** |
| O closed under LGP/T_1 | NOT PROVED |
| S_q output element | FALSE/not source (input pilot) |
| xi-e/f as independent bridge | CIRCULAR |
| D4 extra membership conditions | MISSING |
| explicit actual counterexample | NONE (logical schema only) |

## 8. Conclusion

The corrected domain `S∈VC(I)` removes the container mismatch but not the output bridge. eta equality yields only a volume class `[1*S]=[S_q]` in Rss; it does not yield an element of O, and S_q is an input pilot rather than an output. D4 is therefore rejected; the exact obstruction is the output membership `O∩[S_q]≠∅` (D4-a/b/c), equivalently C1/xi-f. No Lean/mixed/E3; P6 open.

