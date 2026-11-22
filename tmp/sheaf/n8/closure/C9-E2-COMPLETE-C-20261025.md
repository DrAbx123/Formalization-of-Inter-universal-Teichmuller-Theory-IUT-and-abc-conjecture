# C9 E2 construction side: complete C/BPS/Theta for b=273

Task: task-262 (C9-E2-COMPLETE-C-20261025). Owner: logdescent. Date: 2026-10-25. Constructive attack; only this file written; no Lean/Project/target/other-owner edits; no arbitrary data. P6 unproved; target_accepted=false.

Inputs: C9-B273-CONSTRUCTION-20261025.md (SHA256 5353F7E8AF722EDF506F4C567A33CE3332D11FDCDBCBF26D69832491C148D500); C9-B273-COMPLETE-C-20261025.md (task-258); C9-P6-NOGO-20261025.md (task-256); C9-B273-ADMISSIBILITY-20261025.md; C9-ARCH-HULL-20261025.md; C9-IND1-GLOBAL; C9-MOD41-EXACT-G.

## 0. Verdict

The E_546 skeleton can be assembled through E, F, K, the local I_546/b=273 data, the formal C_K/C_F/V/epsilon, and the exact mod41 image. It cannot be completed into an actual source-level C with BPS/Theta/gluing/target data, and it cannot satisfy CFTH/TC/arch, from the frozen source alone.

The obstruction is not a source contradiction and not E1:
- b=273 is admissible at the source-skeleton level (task-258): local I_546, qhat=pi^273 v, e=41, f=1, q-order 273 coprime to41, F degree 2,3-smooth/41-free, exact mod41 G=H=GL2(F41).
- No frozen source condition bounds b, requires b<41, or excludes I_546.
- The E2 escape is therefore not "b=273 impossible"; it is the failure/missing proof of CFTH/TC/arch and of the explicit complete-C/BPS/Theta data. E2 remains OPEN; no P6 counterexample is produced.

First concrete missing source objects, in order:
1. explicit C_F/C_K equations, stacky cusps, 41-division coordinates, K field equations, V places and epsilon cusp coordinates;
2. BPS/Theta-pilot/gluing/target-column data (the source-Theta-pilot is not determined by E_546[41]);
3. corrected finite donor/CFTH finite branch data (H_A-full/B branch);
4. actual archimedean H_C,inf and target-container inclusion (TC-B/TC-C/TC-S);
5. TC-A..TC-H.

A complete C with all these would make P6 false with margin >8800 (task-256), but that C is not constructed. Without them, F(C) is not defined; "E2 failure" is the only live escape but it is not proved as an actual failure for all C.

## 1. What is actually assembled for b=273

From task-257/258:

    E_546: y^2=x^3+(3/M)x+(2/M),  M=1728 p^546-1,  p=12301,
    j=1/p^546,  Delta=-2985984 p^546/M^3,  v_p(Delta)=546.        (1.1)

Local p:
- split multiplicative I_546, q=p^546 u, u in 1+p^546 Z_p;
- q=p^546+744p^1092+O(p^1638) != p^546;
- qhat=q^{1/82}=pi^273 v, v in 1+pZ_p, pi^41=p, qhat^82=q, v_p(qhat)=273/41;
- e=41, f=1; b=273; q-order 273; 41 does not divide 273 or 546.         (1.2)

Field skeleton:
    F0=Q(i,E[6]); [F0:Q] divides 4*288=1152=2^7*3^2;
    F_sem = semistabilization at M-primes and 2,3; F=F0 F_sem;
    F/Q Galois; [F:Q] 2,3-smooth, 41-free; E[2],E[3] full over F; i in F;
    K=F(E[41]); X_K=E_K minus O.                                   (1.3)

Formal C skeleton:
    C_K=[X_K/E[41]] type (1,41-tors)^pm;
    C_F=K-core stack; V section over V_bad={p}; epsilon origin/canonical cusp.  (1.4)

Mod41 (task-258, exact point counts):
    G=H=GL2(F41), |G|=2,755,200; this uses l=37/31 classes and l=7 determinant.  (1.5)

This is a genuine source-level skeleton, but (1.4) is formal and (1.3) is conditional on F_sem's exact degree/existence.

## 2. BPS/Theta attempt

Local BPS data at p can be written concretely from (1.2):
- BPS q-parameter q_BPS = q (or qhat=pi^273v); q-order 273; local type I_546;
- Theta-pilot local shell uses the same q/BPS; the p-adic q is actual and not p^546; B_I-zero arch normalization is independent of b.
This is the full extent of BPS/Theta that E_546 determines: the local p q-parameter and its order. It does not determine:
- the global BPS set/Theta-gluing across all bad places (Vbad only p, but the BPS labels and gluing are source data);
- the target column and fixed q-volume class;
- the Theta-pilot possible-image set or its hull, especially the archimedean component.
There is no source functor from E_546[41] to the BPS/Theta data; assigning q_BPS globally would be arbitrary. The local q-order 273 is actual; the global BPS/Theta package is missing.

## 3. CFTH/TC/arch attempt

CFTH (corrected finite target hypothesis) requires:
- corrected symplectic donor H=Phi^{-1}(Sp), basis alignment, trace target, low ramification, local naturality (task-147/149/165/184);
- finite B=O_K or B=I branch data; task-165/184 show B=O_K/B=I is not determined for full barGamma; H_A-full is not established (E24/W subset J issue);
- exact C_K/C_F/V/epsilon and 41-division field K;
- target-container conditions TC-A..H/TC-S.

For b=273, the local q-order and mod41 data pass, but:
- the finite branch is not actual; CFTH's finite donor identities are not proved;
- the archimedean H_C,inf and its target-container inclusion are missing (task-232/240); only the IV upper bound A_proc=13.164 is known, and it is an upper bound, not an actual hull;
- TC-A..H/TC-S are not supplied.

Therefore CFTH/TC/arch cannot be verified for the b=273 skeleton. If one assumes them, task-256 gives F>8800; but the assumption is exactly E2, not a construction. No source contradiction forces CFTH/TC/arch to fail; they are simply unproved for every actual C. E2 remains an open escape, not a proved failure.

Constructive attempt to avoid CFTH: can one choose a different C or a different target column for b=273? Changing target/column changes the profile and is E3, not an escape for the stated b=273 target. No frozen source condition allows it. Thus E2 is the only honest boundary: either CFTH/TC/arch hold (then P6 false for that C) or they fail (then no counterexample from this profile).

## 4. Consistency checks: no b=273 source contradiction

Checked:
- Def3.1(a): i in F, E[6] full over F. Passes skeleton.
- Def3.1(b): XF once-punctured, stable reduction after F_sem, field of moduli Q, F/F_mod Galois degree prime to41; full E[2]/E[3]. Passes skeleton (exact F degree not computed).
- Def3.1(c): l=41, K=F(E[41]); residue characteristics of Vbad (p=12301) not41; q-order 273 not divisible by41; mod41 image G=H=GL2(F41) exact. Passes skeleton.
- Def3.1(d)-(f): formal C_K/C_F/V/epsilon; explicit equations missing, but no source inconsistency.
- Target/Theta: no frozen target condition bounds b or excludes I_546 (task-258).
No consistency failure found. Hence E2 is not a "b=273 impossible" contradiction; it is a missing-assembly escape.

## 5. Exact E2 escape

The exact E2 escape available from the construction side is:

    E2-C: no actual complete C is assembled because the explicit
    C_F/C_K/V/epsilon, BPS/Theta/gluing/target, CFTH finite branch,
    and actual archimedean target-container data are missing.          (5.1)

At the first missing object level:
- If explicit C_F/C_K/V/epsilon cannot be constructed, E1 (no complete C) may apply, but task-258 shows the source skeleton is admissible, so E1 is not proved;
- If the explicit C data can be constructed but BPS/Theta/target/CFTH/TC/arch cannot, E2 is the escape;
- If CFTH/TC/arch can be constructed for a complete C, P6 is false with margin >8800 (task-256), independent of B branch.

The construction side cannot decide between these; it identifies the exact missing objects. In particular, the local I_546/b=273 data are not the obstruction; the obstruction is global/source-theoretic, not arithmetic.

## 6. Proved / conditional / missing

Proved actual:
- E_546 actual curve, j=1/p^546, Delta, v_p=546, split I_546, q expansion, qhat=pi^273v, e=41,f=1, b=273, q-order 273.
- F0/F_sem/F, K abstract, formal C_K/C_F/V/epsilon skeleton; mod41 G=H=GL2(F41) exact (task-258).
- No source condition excludes b=273; no consistency contradiction found.

Conditional:
- Complete C exists if explicit C_F/C_K/V/epsilon, BPS/Theta/gluing/target, CFTH/TC/arch are supplied.
- Under C1/C2/C3 (task-256), F>8800, P6 false.
- CFTH/TC/arch may hold or fail; not proved either way for actual C.

Missing:
- explicit C_F/C_K/41-division/K field/V/epsilon equations;
- BPS/Theta/gluing/target column/q-volume class;
- CFTH finite branch/H_A-full;
- actual arch H_C,inf and TC-A..H/TC-S;
- complete C.

Impossible/withdrawn:
- deriving BPS/Theta/gluing/target from E_546[41] alone;
- assigning q_BPS/target/arch arbitrarily;
- claiming b=273 excluded by Def3.1 or target conditions (task-258 refutes E1 on those grounds);
- claiming an unconditional P6 counterexample without complete C/CFTH/TC/arch.

## 7. Conclusion

The b=273 E_546 skeleton is admissible but not a complete C. The construction side succeeds through the actual curve, local I_546/b=273, field skeleton and exact mod41 image, and fails at the explicit C_F/C_K/V/epsilon, BPS/Theta/gluing/target, CFTH finite branch, and actual archimedean target-container data. No source consistency failure excludes b=273; therefore the E2 escape is not E1 but the missing global/source data. If those data are supplied, task-256 makes the profile an actual P6 counterexample with margin >8800; if not, E2 remains open and P6 is not refuted. No arbitrary data is used.

Only C9-E2-COMPLETE-C-20261025.md written. No Lean/Project edits. target_accepted=false; P6 conditional no-go, unconditional open.
