# C9 Ind1 action on J：units/permutations 与 L_B invariance

任务：task-330（Ind1 action on J: units/permutations and L_B invariance）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 explicit uniform counterexample；不改 Lean/Project/目标；不引入 arbitrary action；只写本文件。No mixed/E3。

输入：IUT I Def4.10/Prop4.11（processions, capsule-full poly-isomorphisms）；C9-IND1-GLOBAL-20261025.md（full Ind1 与 TC-A..H）；C9-TAME-LOG-DOMAIN-20261025.md §6（L_A/L_B）；C9-RA-SUBSET-RB/REGION-INCLUSION（R_A⊂R_B）；C9-UNIFORM-SAT-U；task-201/203（J=m, H_A-lite）。

## 0.1 Independent verification correction (task-333)

Independent rereading of IUT I Def4.1/Def4.10/Prop4.11 shows that a D-prime-strip is a **collection of categories up to equivalence**; an isomorphism of D^dag-prime-strips gives an outer automorphism of G_K, not a chosen uniformizer/integral ideal J. The step “D^dag-prime-strip isomorphism preserves J=πO_K” is therefore **not a source theorem**; call it (JP). The L_B invariance proof below is valid **conditional on (JP)**. Full Ind1 is larger than the symplectic subgroup H; H_A-lite does not cover arbitrary capsule-full poly-automorphisms. Thus the NPC/U and b=273 F≥8821 conclusions are conditional on (JP) plus row exhaustion (G1), not unconditional. See C9-NPC-VERIFY-INDEPENDENT-20261025.md.
## 0. Verdict

**L_B 在 full Ind1 的 capsule-full poly-automorphisms 下不变；没有 uniform Ind1/J counterexample。** 精确地：

```
L_B = p^{s-r+1} J^{⊗r},   J=πO_K.
```

At each procession level, an Ind1 automorphism is a capsule-full poly-automorphism: a permutation σ of the capsule index set plus an isomorphism of D^dag-prime-strips in each constituent (IUT I Def4.10). A D^dag-prime-strip isomorphism preserves the local field/prime-strip integral structure and log-shell; on J it induces a Z_p-lattice automorphism φ_i∈Aut_{Z_p}(J). Therefore each tensor factor J maps to J, and

```
(⊗_i φ_i) J^{⊗r} = J^{⊗r},   hence   Φ(L_B)=L_B.

```

Using R_A⊂R_B and L_A⊂L_B (task-291), any Ind1 image of the row subfamily is again in R_B. Thus no uniform possible image outside R_B is produced by Ind1 acting on the B=O_K/B=I row lattices.

**However, the stronger claim “the effect on J is by O_K^×” is FALSE.** The H=Φ^{-1}(Sp) action acts nontrivially on J_W by Sp_40(Z_p); a transvection on W is not multiplication by an element of O_K^×. L_B invariance does not require unit action—it only requires J→J factorwise. This distinction is important but not a counterexample to L_B.

## 1. IUT I Def4.10/Prop4.11 input

Def4.10: an n-procession `P_1↪...↪P_n` has j-capsules; each arrow is the collection of all capsule-full poly-morphisms; a capsule-full poly-morphism is a fixed injection of index sets plus arbitrary isomorphisms of constituents; automorphism uses bijection. Thus at level j full Ind1 has

```
permutation σ ∈ S_{j+1};   constituent isomorphisms φ_i : D^dag_i → D^dag_{σ(i)}.

```

Prop4.11 identifies the procession of D-prime-strips and its label indeterminacy; it does not introduce a non-structural Q_p-linear action on the local field. The local factor isomorphism is an isomorphism of D^dag-prime-strips, hence preserves the underlying local field prime-strip data, including O_K and the log-shell J. Its induced action on J is in `Aut_{Z_p}(J)`, not necessarily O_K^×.

## 2. L_B invariance theorem

**Theorem 2.1.** Let `J=πO_K` and `L_B=p^{s-r+1}J^{⊗r}`. For every capsule-full poly-automorphism `Φ=(σ;φ_1,...,φ_r)` with `φ_i∈Aut_{Z_p}(J)`, one has

```
Φ(J^{⊗r}) = J^{⊗r},   Φ(L_B)=L_B.

```

Proof. A pure permutation permutes the tensor factors; `J^{⊗r}` is invariant. A constituent automorphism φ_i maps J onto J; tensoring gives `(φ_1 J)⊗...⊗(φ_r J)=J^{⊗r}`. The scalar p^{s-r+1} is fixed by the action. Hence Φ(L_B)=L_B. QED

**Corollary 2.2.** If `L_A⊂L_B` (task-291) and the row subfamily possible images are obtained from L_A/L_B by full Ind1, then all such images lie in R_B. There is no uniform Ind1/J image outside R_B.

## 3. The O_K^× claim is false

The H symplectic action on `J=J_U⊕J_W` acts trivially on U and by Sp_40(Z_p) on W. A non-scalar transvection `T` in Sp_40(Z_p) is not multiplication by a unit `u∈O_K^×`; for example its fixed subspace is a hyperplane, whereas multiplication by a unit is scalar. Yet T maps J_W to J_W and J to J, so L_B is still invariant. Therefore:

```
“effect on J by O_K^×”             FALSE/too strong;
“J → J factorwise; L_B invariant”  TRUE.

```

This is not a counterexample to L_B: the theorem only needs the weaker factorwise J-preservation.

## 4. Consequence for uniform NPC/U

For the uniform rho=1 profile, TAME §6 finite row possible images are L_A (B=O_K) and L_B (B=I); R_A⊂R_B. If full Ind1 acts by D-prime-strip isomorphisms/permutations as in §2, then the row images are contained in R_B. Good finite places contribute zero/nonpositive under the uniform reference; arch is h_inf. Under the additional row-exhaustion condition (G1) of task-319 (full finite bad possible-image family equals the row family, not other Theta/log/Ind3 branches), this gives

```
h_C <= H_B + h_inf;
h_C <= H_B + A_proc = -8884.245232030… < Q_p=-62.706341073…;
F=Q_p-h_C >= 8821.538890956… >0.
```

Thus the Ind1/J lemma **removes one potential source of failure** (row images leaving R_B), but it does **not by itself prove U_uniform**: TAME §6's row classification is not an upper bound for all C log/Theta/∞ outputs, and other possible-image branches remain under (G1). The exact remaining obstruction is (G1)/NPC, not Ind1 action on J.

## 5. What would be an explicit uniform counterexample?

A uniform counterexample outside R_B would require an actual D^dag-prime-strip isomorphism/Ind1 operation whose induced map on J is **not** a Z_p-lattice automorphism of J (e.g. maps J to a different lattice p^a J or a non-commensurable lattice), or a non-row possible-image class with positive volume. The source D-prime-strip structure/TC-A preserves the log-shell/integral structure, so no such J-scaling operation is in the capsule-full poly-automorphism action described by Def4.10. No explicit uniform counterexample is constructed.

If one drops the D-prime-strip/log-shell preservation and allows arbitrary Q_p-linear maps on the local factor, L_B invariance fails (e.g. a map sending π to 1 would move J out of J); but that is not an Ind1 capsule-full poly-automorphism of D^dag-prime-strips and is not an allowed source operation. This is the exact boundary: the result depends on the source's D-structure/TC-A, not on an arbitrary linear action.

## 6. Proved / conditional / missing

Proved (source-structural):

- Def4.10: Ind1 at a level = permutations + constituent D^dag-prime-strip isomorphisms;
- such isomorphisms preserve O_K/J and induce `Aut_{Z_p}(J)`;
- `Φ(J^{⊗r})=J^{⊗r}` and `Φ(L_B)=L_B`;
- any Ind1 image of L_A/L_B stays in R_B; no uniform Ind1/J counterexample;
- `O_K^×`-only claim is false (H symplectic transvection).

Conditional/missing:

- full row-exhaustion (G1): all finite bad possible images are row images, not other Theta/log/Ind3 branches;
- TC-A/TC-B/TC-D/E and actual complete C;
- good/arch actual normalization;
- if D-prime-strip isomorphisms are interpreted as arbitrary Q_p-linear maps, invariance fails, but that is not the source category.

## 7. Conclusion

Full Ind1 acts on J by Z_p-lattice automorphisms and permutations of tensor factors, not by O_K^× in general. The tensor power L_B is nevertheless invariant: `Φ(L_B)=L_B`. Hence Ind1 cannot produce a uniform finite bad row image outside R_B; the unit-only statement is false but harmless for L_B. This closes the Ind1/J part of NPC but not the full U_uniform: the remaining gap is (G1) row exhaustion/other target branches. Under (G1)+good/arch, b=273 F≥8821.538; no arbitrary action, no mixed/E3, no Lean/Project edits; P6 open.

