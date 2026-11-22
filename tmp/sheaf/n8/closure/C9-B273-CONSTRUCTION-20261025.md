# C9 b=273 local E_j profile: actual construction and exponent correction

Task: task-257 (C9-B273-CONSTRUCTION-20261025). Owner: logdescent. Date: 2026-10-25. Decisive construction; only this file written; no Lean/Project/target/other-owner edits; no arbitrary data. P6 unproved; target_accepted=false.

Input: b=3 E_j profile (task-193/198/229/233); TAME local model q_Tate=qhat^{2l}, qhat=pi^b, pi^41=p, e=l=41.

## 0. Verdict

The literal exponent in the task, j0=1/p^{22386} with 22386=2*273*41, does NOT give the C9 b=273 TAME local profile with e=41. It gives an actual curve with v_p(q)=22386, but q is then a 41st power in Q_p, so the E[41]-extension at p is unramified/trivial (e=1), not e=41. The correct exponent for the C9 b=273 profile is

    N = 2b = 546,   not 2bl = 22386.                                (0.1)

The quantity 2bl=22386 is the exponent of the local uniformizer pi in q: q=pi^{2bl} v^82 = pi^{22386} v^82, while the p-adic valuation is v_p(q)=2bl/e=2b=546. The correct curve is

    E_b273: y^2 = x^3 + (3/M) x + (2/M),   M = 1728 p^546 - 1,      (0.2)

with j=1/p^546, v_p(Delta)=546, local type I_546, q=p^546 u, qhat=q^{1/82}=pi^273 v, and 41 not dividing 273. This is the actual b=273 local profile: qhat^82=q, qhat=pi^273 v with v in 1+pZ_p, qhat not in Q_p, K_v/F_v has e=41, f=1.

Both constructions are recorded below because the task's literal exponent is a meaningful actual curve, but it is not the TAME b=273 profile. No arbitrary data is used: the exponent is forced by the source local model.

## 1. General family

For a positive integer N, define

    M_N := 1728 p^N - 1,
    E_N : y^2 = x^3 + (3/M_N) x + (2/M_N),   j(E_N)=1/p^N.          (1.1)

Equivalently E_N: y^2=x^3 - 3/D_N x - 2/D_N with D_N=1-1728p^N=-M_N. Exact invariants:
- a=3/M_N, b=2/M_N.
- 4a^3+27b^2 = 108(1+M_N)/M_N^3 = 108*1728 p^N/M_N^3.
- Delta = -16(4a^3+27b^2) = -2985984 p^N/M_N^3.
- v_p(Delta)=N, v_p(j)=-N.
At p, E_N has split multiplicative reduction: mod p, M_N=-1, a=-3, b=-2, and the cubic x^3-3x-2=(x+1)^2(x-2); the tangent slopes from the double root are rational (p=1 mod3), so the node is split. The local type is I_N, with Tate parameter q of valuation N.

For N=546=2*273, this gives the C9 b=273 profile; for N=22386=2*273*41, it gives a different actual curve (I_22386) whose E[41]-extension is not ramified of degree41.

## 2. Correct construction N=546 (actual C9 b=273 profile)

    p=12301,   M := 1728 p^546 - 1,
    E_b273 : y^2 = x^3 + (3/M) x + (2/M).                            (2.1)

Exact data:
- j=1/p^546, Delta=-2985984 p^546/M^3.
- v_p(Delta)=546, v_p(j)=-546.
- p-local reduction: split multiplicative I_546; q has v_p(q)=546.
- The E[41] Kummer extension uses q^{1/41}; 546/41 is not an integer (41*13=533, remainder13), so q is not a 41st power in Q_p; the extension K_v/F_v is totally ramified of degree e=41. Since p=1 mod41, mu_41 subset Q_p, so f=1.
- q/p^546 in 1+pZ_p; write q=p^546 u with u in 1+pZ_p (indeed q/p^546 in 1+p^546Z_p).

Tate q-expansion:
    j(q)=q^{-1}+744+196884q+...
    q = p^546 + 744 p^1092 + O(p^1638).                              (2.2)
So q != p^546; exact q is a p-adic unit multiple of p^546.

qhat:
p=12301 does not divide 82; the 82nd-power map on 1+pZ_p is bijective. Let v in 1+pZ_p be the unique element with v^82=q/p^546. Let pi be the uniformizer of the E[41] local field with pi^41=p (K_v contains pi from q^{1/41}; 41 is prime to 6 and gcd(13,41)=1). Then

    qhat := q^{1/82} = pi^273 v,   qhat^82 = q,
    qhat = pi^273 v,   v in 1+pZ_p.                                  (2.3)

Therefore the TAME exponent is b=273: qhat=pi^b v, qhat not in Q_p (valuation273/41), qhat^82=q, and q=pi^{22386}v^82. The p-adic valuation is v_p(q)=22386/41=546=2b; the pi-exponent is 2lb=22386. Both numbers have different meanings; only 546 is the p-adic valuation.

This proves the b=273 local profile is actual: E_b273/Q is an actual elliptic curve with split multiplicative I_546 at p, qhat=pi^273 v, order/exponent b=273, and e=41,f=1.

Mahler-Manin checks:
- j(E_b273)=1/p^546 is rational, so E_b273 is defined over Q; this is not the forbidden q=p^22386 rational-j assumption.
- q is the p-adic Tate parameter, not an algebraic number: if q were algebraic, J(q)=j(E_b273) would be transcendental by p-adic Mahler-Manin (q algebraic, 0<|q|_p<1), contradicting j(E_b273) in Q. Hence the exact q is transcendental, consistent.
- q is not p^546; the inversion formula (2.2) has the infinite tail 744p^1092+...
- qhat exists because q/p^546 is a unit in 1+pZ_p and 82 is invertible on that group; qhat is in K_v, not in Q_p.

Complete-C skeleton:
- F0=Q(i,E_b273[6]); [F0:Q] divides 4*288=1152=2^7*3^2, prime to41; full E[6] over F0; i in F0.
- F_sem: semistabilization at the primes of M and at 2,3; formal finite extension of degree with prime factors 2,3; F=F0 F_sem; F/Q Galois, 41 not divide [F:Q]; E_b273/F stable at finite places.
- K=F(E[41]), X_K=E_K minus O; C_K=[X_K/E[41]] type (1,41-tors)^pm; C_F K-core; Vbad after semistabilization is {p}; V section over p; epsilon the origin/canonical cusp.
- Explicit C_F/C_K/V/epsilon equations, K field equations, mod41 image, exact factorization of M, and the complete-C BPS/Theta/target data remain missing; the skeleton is formal, not a complete C.

## 3. Literal task curve N=22386: actual but not e=41/b=273 TAME

Take N=22386=2*273*41:

    M' := 1728 p^22386 - 1,
    E_lit: y^2=x^3+(3/M')x+(2/M'),   j=1/p^22386.                   (3.1)

Actual local data:
- v_p(Delta)=22386; split multiplicative I_22386; q has v_p(q)=22386.
- q=p^22386+744p^44772+...; q/p^22386 in 1+pZ_p.
- qhat=q^{1/82}=p^273 v (v in 1+pZ_p), because 22386/82=273 is an integer; hence qhat is in Q_p, not in a ramified K_v.
- q^{1/41}=p^546 v^{1/41} is also in Q_p (41st root of the unit exists in 1+pZ_p, and 22386/41=546). Therefore all E[41]-torsion is defined over Q_p (mu_41 subset Q_p), and K_v=F_v; e=1, not41.
- If one writes qhat=pi^b with pi^41=p, then qhat=p^273 v=pi^{273*41}v=pi^{11193}v, so b_pi=11193, not273. The number273 is the p-exponent, not the TAME pi-exponent.

Thus N=22386 is an actual elliptic curve with I_22386 and a p-adic qhat of p-exponent273, but it does NOT realize the C9 b=273 local profile with e=41. The task's formula v_p(q)=2*b*l=22386 is the pi-exponent, not the p-adic valuation; the correct p-adic valuation for b=273 is 2b=546.

This is a decisive correction, not an arbitrary choice:
- TAME: q_Tate=qhat^{2l}, qhat=pi^b, pi^41=p; q_Tate=pi^{2lb}, v_p(q_Tate)=2lb/41=2b.
- For b=273: v_p(q)=546, pi-exponent=2*41*273=22386.
- Setting v_p(q)=22386 gives pi-exponent=22386*41=917826, not22386, and qhat=pi^{917826}? qhat=q^{1/82} valuation=22386/82=273; qhat=pi^{273*41}=pi^{11193}, not pi^273.

## 4. Mahler-Manin and exact-q issues for both

For either N, E_N is defined over Q and j=1/p^N is rational. The exact q is the p-adic Tate parameter of E_N; it is not a rational/algebraic number automatically:
- If q were algebraic, p-adic Mahler-Manin would make J(q)=j(E_N) transcendental over Q, contradiction with j(E_N) in Q.
- Therefore q is p-adic transcendental; no algebraic exact q=p^N or p^N u is assumed.
- The q-expansion inversion has q=p^N+744p^2N+...; q/p^N is in 1+p^N Z_p, not equal1.
- For N=546, qhat=pi^273 v is not in Q_p; for N=22386, qhat=p^273v is in Q_p and e=1. This is the exact distinction relevant to C9.

## 5. Proved / conditional / missing

Proved actual:
- E_b273: y^2=x^3+(3/M)x+(2/M), M=1728p^546-1; j=1/p^546; Delta=-2985984p^546/M^3; v_p(Delta)=546; split multiplicative I_546; q=p^546+744p^1092+...; qhat=pi^273v; qhat^82=q; qhat not in Q_p; e=41,f=1; b=273 TAME profile actual.
- E_lit with N=22386 is actual with I_22386 and qhat=p^273v, but e=1, b_pi=11193; not the C9 b=273 e=41 profile.
- TAME exponent relation v_p(q)=2b, pi-exponent=2lb; correct exponent N=2b=546.
- Mahler-Manin consistency: j rational, q transcendental, q not p^N.

Conditional/standard:
- Semistabilization at the primes of M and 2,3; exact factorization of M and exact F_sem degree not computed.
- F0/F/K/C_K/C_F/V/epsilon source-level skeleton exists; explicit equations, K field, mod41 image not computed.
- The complete C and BPS/Theta/target data are missing.

Missing:
- Explicit factorization of M_546/M_22386 and bad sets;
- exact C_F/C_K/V/epsilon equations and K field;
- mod41 image;
- complete C, weights, target.

## 6. Conclusion

The actual b=273 local E_j profile exists with exponent N=2b=546:

    E: y^2=x^3+3x/M+2/M, M=1728p^546-1,
    v_p(q)=546, qhat=q^{1/82}=pi^273 v, e=41,f=1.

The literal N=22386 curve is actual but has e=1 and pi-exponent11193; it does not realize the C9 b=273 e=41 profile. The task's "v_p(q)=2*b*l=22386" conflates the pi-exponent with the p-adic valuation; the correct p-adic value is 2b=546, and the pi-exponent is 2bl=22386. Mahler-Manin is consistent in both cases: j is rational and q is transcendental. A complete C skeleton can be formally built as in the b=3 case, but explicit C/K/V/epsilon and mod41 data remain missing. No arbitrary data was used; the exponent correction is forced by TAME.

Only C9-B273-CONSTRUCTION-20261025.md written. No Lean/Project edits. target_accepted=false; P6 open.
