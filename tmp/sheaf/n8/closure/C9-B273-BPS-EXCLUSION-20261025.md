# C9 b=273 exclusion via BPS/Theta/q-order

任务：task-284（Attack b=273 exclusion via BPS/Theta/q-order）。owner：iplsheapt。日期：2026-10-25。短定理/证明或 exact obstruction；不改 Lean/Project/目标；不引入 arbitrary BPS data；只写本文件。

输入：C9-B273-ADMISSIBILITY-20261025.md；C9-B273-COMPLETE-C-20261025.md；C9-B273-EXCLUSION-20261025.md；C9-B273-CONSTRUCTION-20261025.md；C9-IND1-GLOBAL-20261025.md；IUT I Def3.1(c)/IUT III Theta-pilot/BPS structures。

## 0. Verdict

**BPS/Theta/q-order 不能排除 b=273。** 当前 frozen source 中所有可用的 q-order/BPS/Theta/target-column 约束只有：

```
(Q1) l=41 is prime to the bad q-orders and residue characteristics;
(Q2) qhat=q^{1/(2l)} exists; the local type is tame I_{2b};
(Q3) Theta/BPS weights are rho^{j+1}, j=1,...,20, rho=1 uniform;
(Q4) BPS/Theta q-power orders at level j are b times exponents built from j
     (j, triangular j(j+1)/2, or products of factors <=20);
(Q5) target-column normalization is B_I-zero, independent of b.
```

b=273 satisfies all: `gcd(273,41)=1`, `gcd(2·273,41)=1`, local I_546, qhat=π^273 v, and at j≤20 none of the level exponents is divisible by41. There is no frozen BPS/Theta inequality bounding b or excluding I_546. Hence **E1 is not proved by this angle**; the exact obstruction is the missing complete BPS/Theta-pilot/gluing/target-column construction, not a b=273 arithmetic defect.

## 1. Q-order and local type

E_{546}: `j=1/p^{546}`, `v_p(Δ)=546`, split multiplicative `I_546`, `q=p^{546}u` with `u∈1+p^{546}Z_p`. Since p=12301∤82, there is v∈1+pZ_p with

```
qhat=q^{1/82}=π^{273}v,   qhat^{82}=q,   v_pi(qhat)=273/41,
qhat^2=q^{1/41}=π^{546}.
```

Thus the q-order/exponent is `b=273=3·7·13`; the discriminant exponent is `2b=546`. `l=41` divides neither. The residue characteristic p=12301 is not41. The local type is `I_546`, not `I_6`; that is a different b-profile, not an inadmissibility. This is the same check as the Def3.1(c) admissibility; BPS/Theta adds no new divisibility.

## 2. BPS/Theta level exponents and l=41

At Theta-pilot level j (j=1,...,m=20), the standard exponents are j and triangular `T_j=j(j+1)/2`; BPS q-exponents are products of these/factors ≤20. The exact list of `T_j` is

```
1,3,6,10,15,21,28,36,45,55,66,78,91,105,120,136,153,171,190,210.
```

None is divisible by41 (the first multiple 41 is not in this list; 205 would be a multiple but is not triangular). For j≤20, j itself is not divisible by41. Hence any BPS q-order of the form `b·T_j` or `b·j` has 41-adic valuation 0, because `41∤273` and `41∤T_j,j`. Theta weights `rho^{j+1}=1` introduce no q-order. The target q-volume class doesn't impose an integer b-bound; it is a volume/normalization class, not an order divisibility.

### BPS/Theta order lemma

**Lemma 2.1.** For every j=1,...,20: `gcd(273·j·T_j,41)=1`; all BPS/Theta q-orders built from these exponents are prime to l. **Proof:** 41 prime, 41∤273 and 41∤j,T_j as listed; product remains coprime. QED

This is why q-order/BPS/Theta cannot exclude b=273: the l-coprimality condition is **satisfied**, not violated.

## 3. What a BPS/Theta exclusion would need

To exclude b=273 beyond Def3.1, one would need an actual BPS/Theta-pilot/gluing/target-column invariant `I(BPS,Theta)` with a proved inequality `I<...` or an integrality condition violated by b=273. The frozen source supplies only:

```
- local q-order and qhat existence (satisfied);
- weights rho^{j+1} (satisfied);
- target-column/normalization B_I-zero (b-independent);
- no inequality b<l, no weight positivity/bound on b, no q-order congruence b≡... .
```

No such invariant is constructed. Assigning an arbitrary BPS/Theta weight, q-volume, or target column to force b=273 out would be an arbitrary assumption, prohibited. Therefore the exact obstruction is **not an arithmetic contradiction**; it is the missing complete BPS/Theta/gluing/target-column data.

## 4. Could one construct the missing BPS/Theta data for b=273?

The BPS/Theta-pilot/gluing/target-column data are not functions of the local q-order. They require:

```
(D1) the actual global complete C and its Theta-pilot object;
(D2) the fixed BPS gluing and target column;
(D3) the q-volume class and log-theta-lattice;
(D4) compatibility with the E[41]/K/C_F/C_K/V/epsilon construction.
```

For E_{546}, (D1)-(D4) are missing, exactly as for b=3. The q-order 273 does not determine them; constructing them from q alone would be arbitrary. So this angle yields no exclusion and no complete C. E1 remains unproved.

## 5. Exact theorem

**Theorem 5.1 (no BPS/Theta/q-order exclusion).** Under the frozen source constraints, the b=273 profile satisfies all q-order/BPS/Theta constraints; no such constraint excludes it. More precisely: `41∤273`, `41∤546`, local type I_546, qhat=π^273v, BPS/Theta exponents at j≤20 are prime to41, weights rho^{j+1}=1, target normalization is b-independent. Hence any claimed exclusion of b=273 from these data is unsupported unless it adds a new BPS/Theta invariant with an explicit inequality/integrality violating b=273. No such invariant is in the current corpus.

**Corollary 5.2.** E1 (no admissible complete C with b=273) is not proved by this angle. A complete C with b=273 is also not constructed: the missing objects are (D1)-(D4), not a b=273 q-order defect. The only live escape from the b=273 no-go remains E2 (CFTH/TC/arch failure), not a BPS/Theta/q-order exclusion.

## 6. Proved / conditional / obstruction

Proved exact:

- 41∤273 and 41∤546; I_546; qhat=π^273v;
- triangular exponents T_j (j≤20) are not divisible by41;
- BPS q-orders b·j·T_j are all prime to41;
- Theta weights rho^{j+1}=1; target normalization independent of b;
- no frozen BPS/Theta constraint bounds b or excludes I_546.

Conditional/missing:

- actual BPS/Theta-pilot/gluing/target-column data;
- complete C; CFTH/TC/arch;
- any new BPS/Theta invariant with a valid exclusion inequality.

Obstruction:

- No source theorem gives a BPS/Theta/q-order exclusion of b=273;
- constructing BPS/Theta from q-order alone is impossible/arbitrary;
- E1 remains unproved; complete C remains missing.

## 7. Conclusion

The BPS/Theta/q-order attack does **not** exclude b=273. The q-order is 273, l=41 coprime, local I_546, qhat=π^273v; all level BPS/Theta exponents j, T_j (j≤20) are prime to41; weights/target normalization are b-independent. The exact obstruction is the absence of a complete BPS/Theta-pilot/gluing/target-column construction and of any new invariant that could bound b. No arbitrary BPS data are introduced; no Lean/Project edits; P6 open.

