# C9 uniform b=273: E1 exclusion or complete C/BPS

Task ID: task-322 / C9-UNIFORM-B273-EXCL-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Scope: fixed F_mod=Q, uniform profile rho=1, selected places only. Mixed rho/E3 profiles are excluded. No Lean/Project edits; no arbitrary data; only this file written.

## 0. Inputs

- C9-B273-ADMISSIBILITY-20261025.md, SHA256 1492f6d1b87ffad66639c5f2244d0db88cb490748f394ebabda92a3aa97f62ff.
- C9-B273-EXCLUSION-20261025.md, SHA256 e792e271b440ca0f65908e7de943ce109f47c90ac0c1dd399e52a42a93bbce9f.
- C9-E2-TC-CFTH-20261025.md, SHA256 b3321c4e5431c9d59f04fd46e4b6662f2ace0d95d67de44a84e199ff9d335fe2.
- C9-B3-SATURATION-20261025.md, SHA256 b32a524b3f5275561f2db16d3716c245e88151fcd3045a14d5c4b68d357d5eae.
- C9-MASTER-V4-20261025.md, SHA256 e89d13443fd8f020ee56871427d0cf433a18d2ff5f8ae0c7b94a449161cd2db5.
- C9-GLOBAL-BPS-ENV-20261025.md, SHA256 5c1a3ae53f47ce7bcc3cdb294169d3b3034303e05fe93108210cd79b678c422e.

## 1. Short theorem

**Theorem (uniform b=273 status).**

(a) **E1 is not proved.** Under the fixed uniform profile, the E_546 curve

      E: y^2=x^3+(3/M)x+(2/M),  M=1728 p^546-1,  p=12301,          (1.1)

    has j=1/p^546, v_p(Delta)=546, split I_546, q=p^546u, qhat=pi^273v, b=273, e=41, f=1; q-order 273 is prime to l=41. It passes IUT I Def3.1(a)-(c) at source-skeleton level, including the 2,3-smooth 41-free field and mod-41 G=H=GL2(F41). No uniform Def3.1, q-order, residue-characteristic, or Theta condition excludes b=273.

(b) **A complete uniform C/BPS with b=273 is not constructed.** The missing objects are the global BPS/Theta-pilot environment, explicit C_F/C_K/V/epsilon, the uniform B/I and saturation/target data, CFTH/TC-A..TC-H/TC-S, and actual archimedean H_C,inf. These are not functions of E_546 alone.

(c) **Conditional upper-side replacement.** If a complete uniform C with b=273 is supplied, and if the uniform saturation upper U273

      h_C <= max(H_A,H_B)+h_inf                                  (1.2)
      H_A=-(39156/41)log p, H_B=-(38736/41)log p,                 (1.3)

    holds together with CFTH/TC/arch, then P6 is false with margin

      Q_C-h_C >= (38883/41)log p - h_inf >= 8918.01 > 0        (1.4)
    in the B=O_K branch, and at least 8821.54 > 0 in the B=I branch. (U273 is an upper, not a lower, saturation theorem; it is not proved in the frozen source.)

(d) **Without E1 or U273**, no uniform b=273 conclusion follows: E1 remains open, no actual counterexample is produced, and the upper-side repair is conditional. This is the exact status.

## 2. Proof of the source checks

### 2.1 Def3.1(a),(b): field and stable reduction

F0=Q(i,E[6]); F_sem is the semistabilization compositum at M-primes and 2,3; F=F0 F_sem; K=F(E[41]). For q|M, E_546 has (v(c4),v(c6),v(Delta))=(3,5,9), Kodaira III*, semistabilization degree 4; the M-part of F_sem is a 2-power. At 2 the type is I0 (degree1), at 3 I0* (degree2). Thus [F:Q] is 2,3-smooth and 41-free; F/Q is Galois and contains i,E[6]. E_546 has stable reduction over F. Def3.1(a) and the field/stable-reduction part of (b) hold at skeleton level.

### 2.2 Def3.1(c): q-order and residue characteristic

p=12301, q=p^546u, qhat=pi^273v, qhat^82=q, qhat^2=pi^546. The q-order is 273=3*7*13; 41 divides neither 273 nor 546; p!=41. The local type is I_546. Thus l is prime to the residue characteristic and q-order. This is not an inadmissibility.

### 2.3 Def3.1(c): mod-41 image

Reducing E_546 mod 41 and counting points gives projective orders 7 and 5 and determinant order 40; Dickson's classification excludes all proper maximal subgroups of GL2(F41), so G=GL2(F41). F is unramified at 41 (E_546 good at41; F0 ramified only at2; F_sem at2,3,p,M-primes), so F cap Q(zeta_41)=Q and H=GL2(F41). The image condition holds for the skeleton.

### 2.4 Def3.1(d)-(f), BPS/Theta

The formal C_K=[X_K/E[41]], C_F, V section over Vbad={p}, epsilon origin/canonical cusp exists at stack/formal level as in the b=3 case. No uniform source condition bounds b or excludes I_546. BPS/Theta constraints only require q-order coprimality and weights rho^{j+1}=1; both hold. Thus no uniform BPS/Theta/q-order exclusion of b=273 exists.

## 3. Why the complete C is missing

The first missing source objects, in uniform scope, are:

1. explicit C_F/C_K equations, stacky cusps, 41-division coordinates, K field equations, V/epsilon places;
2. the global BPS/F^{⊩▶×mu} labels/gluing and Theta-pilot 0-column, including mono-theta environments and Kummer evaluation data;
3. the uniform B/I branch and saturation/target upper U273 (TC-B/TC-C);
4. CFTH/TC-A..TC-H/TC-S;
5. actual archimedean H_C,inf (only the upper container A_proc=13.164 is known).

None is a function of E_546[41] or of the local q-order. BPS is an input to the multiradial algorithm, not an output of the curve; assigning BPS labels/gluing or U273 by hand would be arbitrary and is excluded.

## 4. Exact obstruction and classification

ACTUAL (uniform):

- E_546 actual curve, local I_546/b=273, qhat=pi^273v, q-order 273;
- Def3.1(a)-(c) skeleton checks, mod-41 GL2 image;
- uniform finite values H_A,H_B and arch upper A_proc.

CONDITIONAL:

- complete uniform C with BPS/Theta + CFTH/TC/arch;
- saturation upper U273;
- conditional P6 counterexample margins (1.4).

MISSING / EXACT OBSTRUCTION:

- global BPS/Theta-pilot environment; explicit C_F/C_K/V/epsilon;
- uniform B/I and saturation upper U273; TC-A..H/TC-S; actual arch H_C,inf;
- no E1 proof and no complete C.

WITHDRAWN:

- E1 exclusion of b=273 from Def3.1/q-order/BPS/Theta;
- unconditional b=273 counterexample;
- any mixed/E3 profile rescue or refutation.

## 5. Verdict

**E1 is not proved.** The uniform b=273 profile passes the source-level Def3.1/q-order/BPS/Theta checks. A complete uniform C/BPS is also not constructed: the exact obstruction is the global BPS/Theta environment plus saturation/TC/arch data, not a b=273 arithmetic defect. If such a C and U273 are supplied, b=273 gives a conditional P6 counterexample with margin >8800; otherwise the uniform P6 question remains open. No mixed/E3 profile is used.

Status: short natural-language theorem/proof; no Lean/Project edits; no arbitrary data. target_accepted=false; P6 unconditional open.
