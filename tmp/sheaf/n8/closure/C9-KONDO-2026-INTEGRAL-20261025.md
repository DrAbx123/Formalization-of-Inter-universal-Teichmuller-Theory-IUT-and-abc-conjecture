# C9 Kondo 2026 source mining：integral basis / primitivity / A=1

任务：task-356（Mine Kondo 2026 for integral basis/primitivity/A=1）。owner：iplsheapt。日期：2026-10-25。短审计；不改 Lean/Project/目标；不引入 arbitrary normalization；只写本文件。No mixed/E3。

输入：Kondo 2026 本地快照 `sources/Kondo-2605.25428v2.html`（SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86）；Kondo 2025 `sources/Kondo-2512.09231v1.html`；C9-NEW-BI-SOURCE-20261025.md；C9-B273-*；C9-RA-SUBSET-RB。

## 0. Verdict

**Kondo 2026 不提供 integral Z_p-basis、y1 primitivity、A=v_p(Tr y1)=1 或 U-lattice normalization。** 它只给 `k_+(G)` 的 **Q_p-basis** `y_1,...,y_d`，并把 `Aut_{Q_p}(k_+)` 与 `GL_d(Q_p)` 等同；没有 `O_K/Z_p/π/J` lattice 或 integral change-of-basis。因此 kappa/B=O_K/B=I 不能从该 source 决定；精确 gap 是 integral lattice/primitivity/A 三项，均缺失。

## 1. What Kondo 2026 actually says

Theorem 1.3 (source): the `d(G)` elements `y_1,...,y_{d(G)}` form a basis of the **Q_{p(G)}-vector space** `k_+(G)`; for odd `d_k`, the trace-kernel is spanned by `y_2,...,y_{d_k}`. The paper then equips `k_+` with this basis to identify

```
Aut_{Q_{p_k}}(k_+) ≅ GL_{d_k}(Q_{p_k}).
```

This is a **Q_p-linear** statement. The source's `Z` (or similar group) is the image of `Q_{p_k}[Gal(k/k^{(d=1)})]^×` in `GL_{d_k}(Q_{p_k})`; it is not a Z_p-lattice basis of `J=πO_K`, not a primitivity normalization of `y_1`, and not an integral polarization. The normalized Haar measure on `Out(G_k)` is unrelated to a U-lattice.

A direct search of the 2026 snapshot finds no occurrence of:

```
integral Z_p-basis / Z_p-span of J / O_K-basis;
y_1 primitive in J/pJ (or in O_K/pO_K);
A := v_p(Tr(y_1)) = 1;
kappa := e·v_p(Tr y_1) − v_pi(y_1);
U-lattice normalization.
```

Kondo 2025 Theorem 1.3 likewise gives only the Q_p trace-kernel span; no integral normalization.

## 2. Consequence for kappa/B

The C9 kappa theorem uses

```
y_1=a p+l,  l∈L=J∩W,  Tr(y_1)=a·41p,  kappa=41−v_pi(y_1)
```

and requires `a∈Z_p^×`, i.e. `A=v_p(Tr y1)=1` plus a primitive `y1`. Kondo 2026 does not fix `a` or the integral representative of `y1`; a Q_p-basis can be rescaled by any `GL_d(Q_p)` without changing the basis theorem. Therefore:

```
no A=1; no primitivity; no kappa computation; no B=O_K/B=I selection.
```

The anti-diagonal trace Gram is also not in Kondo 2026; the only source-level facts are the Q_p basis and trace-kernel span. Any Z_p-basis/Gram normalization is an extra input, not a source theorem.

## 3. Exact missing source data

To decide B, one would need one of:

```
(I1) a Z_p-basis of J (or O_K) containing y_1,...,y_d with an integral change-of-basis matrix;
(I2) a source proof that y_1 is primitive in J/pJ (a∈Z_p^×);
(I3) a source normalization A=v_p(Tr(y_1))=1;
(I4) a U-lattice normalization fixing the trace line Q_p1.
```

None appears in Kondo 2025/2026. The current Q_p basis theorem is compatible with many integral representatives and many kappa values; it cannot select [0,40] or B.

## 4. Classification

| item | status |
|---|---|
| y_1,...,y_d Q_p-basis / trace kernel | PROVED source (Kondo 2025/2026) |
| integral Z_p-basis / O_K-basis | NOT IN SOURCE |
| y_1 primitivity / A=1 | NOT IN SOURCE |
| kappa / B=O_K/B=I | NOT DECIDED |
| anti-diagonal Gram | NOT IN SOURCE |
| U-lattice normalization | NOT IN SOURCE |

## 4.5 Consequence for actual B=I and R_B⊂H_C

For b=3, the actual B=I route requires the exact branch data `A=v_p(Tr y1)=1` and `y1` primitive, giving `kappa∈[1,40]`; then TAME/TC-B would put the B=I row region R_B into H_C and yield

```
H_B=9/41 logp,   Q_p=-3/41 logp,   S_3=12/41 logp;
R_B⊂H_C ⇒ h_C≥H_B+h_inf;
h_inf≥-S_3 ⇒ h_C≥Q_p (P6).
```

Kondo 2026 supplies none of these integral/normalization facts. Therefore:

- actual B=I is **not proved**; kappa remains missing;
- R_B is only a conditional lattice formula, not an actual possible image;
- R_B⊂H_C and the b=3 P6 conclusion remain conditional on the missing A=1/primitivity plus actual TC-B and h_inf≥−S3.

The exact source gap for b=3 P6 is the conjunction of (I1)-(I4) above and the target/arch inputs of C9-P6TRUE-RB-HULL. No integral normalization can be chosen by hand.
## 5. Conclusion

Kondo 2026 supplies only a Q_p-basis of k_+ and Q_p-linear automorphism identification; it does not supply an integral Z_p-basis, primitivity of y1, A=v_p(Tr y1)=1, or a U-lattice normalization. Thus kappa/B cannot be decided from this source. The exact gap is (I1)-(I4); any integral/primitive choice is a new source input, not a consequence of Kondo 2026. No mixed/E3, no arbitrary normalization; no Lean/Project edits; P6 open.

