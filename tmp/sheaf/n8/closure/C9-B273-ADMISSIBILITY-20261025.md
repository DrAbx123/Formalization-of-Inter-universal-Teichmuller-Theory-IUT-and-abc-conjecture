# C9 b=273 admissibility: source skeleton, no exact exclusion

Direct decisive work. Date: 2026-10-25. Owner: kummer.
Short theorem/proof; no audit, no Lean/Project edits, no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs and question

- C9-P6-NOGO-20261025.md (task-256), 181 lines,
  SHA256 7b9bb3256363b6a8d0931e4e55c62d6ffa27e1fd2a0bf421dc35744d9167557d.
- C9-CONSTRUCT-KCK-20261025.md (task-193), 174 lines,
  SHA256 e250d5c545ac6f152275b0fc9ec0e4966ff2917318d01b4c684143645c7fd40a.
- C9-MOD41-EXACT-G-20261025.md (task-231), 214 lines,
  SHA256 443a59656b1c1a7ddf3e921307fdfae54beaf50cdaf4542624ab3fd3a1b18ecc.
- C9-MOD41-UNCONDITIONAL-20261025.md (task-236), 204 lines,
  SHA256 4eaf8135eff70d6d5d79b6eb66a250f58b04a1e3ff4da6210624684a4d6f9c25.
- C9-P6-SIGN-AUDIT-20261025.md (task-254), 242 lines,
  SHA256 f4797c04cc87f6397cb15a5a4355b22dbea179fc5895cd06af1de774918409a9.

Question: is there an admissible complete C with the b=273 profile at
p=12301, or is E1 (no such C) true? We test IUT I Def3.1(c) q-order,
l=41 coprimality, local I_546, F/K degrees, mod-41 image, and target/Theta
conditions.

## 1. Verdict

**The b=273 profile is not excluded by the source conditions.** A source-level
skeleton exists:

    E_{546}: y^2 = x^3 - 3/D x - 2/D,
    D = 1-1728 p^{546},  p=12301,
    j(E_{546}) = 1/p^{546},  v_p(Delta)=546,
    local type I_546,  q=p^{546}u,  qhat=pi^{273}v,  b=273.       (1.1)

The q-order conditions pass: l=41 does not divide 273 or 546; the local type
is I_546; the global field F=Q(i,E[6],F_sem) has 2,3-smooth degree prime to 41;
the mod-41 image is G=H=GL2(F41) (exact point counts below); and no
target/Theta condition in the frozen source bounds b or excludes b=273.

Therefore **E1 is not proved**. There is a source-level skeleton, but not a
fully explicit complete C: C_F/C_K/V/epsilon equations remain formal as in the
b=3 case. The only live escape from the task-256 b=273 no-go is **E2** (failure
of CFTH/TC/arch target inputs), not exclusion of the profile. An actual complete
C would make the b=273 no-go an actual P6 counterexample.

## 2. Local p data: I_546 and b=273

For E_{546}, with D=1-1728p^{546}:

    a=-3/D, b=-2/D, Delta=2985984 p^{546}/D^3,  v_p(Delta)=546.   (2.1)

The Tate q-expansion inversion gives

    q = p^{546}+744 p^{1092}+O(p^{1638}) != p^{546},
    q/p^{546} in 1+p^{546}Z_p subset 1+pZ_p.                       (2.2)

Since p=12301 does not divide 82, the 82nd-power map on 1+pZ_p is bijective;
let v in 1+pZ_p with v^{82}=q/p^{546}. Then

    qhat := q^{1/82}=pi^{273} v,  qhat^{82}=q,
    qhat^2 = q^{1/41}=pi^{546},  v_p(qhat)=273/41.                 (2.3)

Thus qhat is an integral power pi^{273} times a unit, b=273, local type
I_546, e=41, f=1. The local q-order is 273; l=41 does not divide 273, and
l=41 does not divide 2b=546. IUT I Def3.1(c) q-order condition passes. The
local type is I_546, not I_6; that is a different b-profile, not an
inadmissibility.

## 3. Global field F/K and Def3.1(a)(b)

Let

    F0=Q(i,E[6]),  F_sem=semistabilization compositum,  F=F0*F_sem,
    K=F(E[41]).                                                       (3.1)

For D-primes q|D, E_{546} has (v(c4),v(c6),v(Delta))=(3,5,9), Kodaira III*,
semistabilization degree 4; the D-part of F_sem is a 2-power. At 2 and 3 the
local types are the same as for E_j b=3: p=2 I0 good degree1; p=3 I0* additive
quadratic degree2. Therefore

    [F:Q] is 2,3-smooth and 41 does not divide [F:Q],                 (3.2)

F/Q is Galois (F_sem is the Galois semistabilization compositum). This
verifies Def3.1(a) (i in F, E[6] over F) and the field/degree part of (b) at
source-skeleton level. Exact [F:Q] is not computed, but the prime support is
only 2,3.

The geometric construction X_K=E_K minus O, C_K=[X_K/E[41]], C_F, V section,
epsilon origin/canonical cusp is the same source-level construction as in
task-193; explicit equations/stacky points remain missing (not an
admissibility exclusion).

## 4. Mod-41 image: exact G=H=GL2(F41)

For E_{546}, reduce mod l and count with the standard Legendre sum:

    #E(F_l)=l+1+sum_x chi(x^3+a x+b),  a=-3/D mod l, b=-2/D mod l.

Exact results:

| l | D mod l | a | b | #E(F_l) | a_l | t_l mod41 | d_l |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 7 | 2 | 2 | 6 | 11 | -3 | 38 | 7 |
| 31 | 9 | 10 | 17 | 41 | -9 | 32 | 31 |
| 37 | 2 | 17 | 36 | 32 | 6 | 6 | 37 |

Projective orders and discriminants:

- l=37: charpoly x^2-6x+37, Delta=11 mod41 nonsquare, projective order 7;
- l=31: charpoly x^2-9x+31? Wait t=-9=32, d=31; x^2-32x+31,
  Delta=32^2-4*31=900=39 mod41 square, projective order 5;
- l=7: determinant 7 has order 40 in F41^times.

Dickson exclusion: the nonsquare/order-7 class at l=37 excludes Borel, split
Cartan and exceptional maximal subgroups (all indices 42, 861, 114800, 57400,
22960 contain 5 or 7); the square/order-5 class at l=31 excludes the nonsplit
Cartan normalizer (index 820 contains 5). Hence

    SL2(F41) subset G.                                             (4.1)

The l=7 determinant has order 40, so det(G)=F41^times. With SL2 subset G,

    G=GL2(F41),  |G|=2,755,200.                                    (4.2)

Over F: F/Q is unramified at 41 (E_{546} has good reduction at 41 since
D mod41=36!=0; Q(i) ramified only at 2; F_sem at 2,3,p,D-primes), hence
F cap Q(zeta_41)=Q and det(H)=F41^times. Since [F:Q] is 2,3-smooth, the same
PSL2-simplicity/SL2-transfer argument as E46 gives H=GL2(F41). Thus the mod-41
clause (c) is verified unconditionally for this skeleton.

## 5. Target/Theta and Def3.1(c) decision

IUT I Def3.1(c) requires l prime to the residue characteristics and to the
q-orders at bad places. At p=12301: residue characteristic p !=41; q-order
273, 41 does not divide 273. At D-primes: potential good additive, no
q-parameter; 2,3: after semistabilization good. So no clause (c) exclusion.

The Theta-pilot/target data use b only through the qhat exponent and the local
type; the B_I-zero arch bound A_proc is independent of b. No frozen target or
Theta condition bounds b, requires b<l, or excludes I_546. The b=273 profile
is therefore **admissible at the source-skeleton level**.

What is missing is not admissibility but a fully explicit complete C:
C_F/C_K/V/epsilon equations, stacky points, 41-division coordinates, exact
[F:Q], and the complete target/BPS/Theta data. These are the same missing
items as for b=3; they do not prove E1.

## 6. Decision

- **E1 (no admissible C with b=273): NOT PROVED and structurally disfavored.**
  The explicit E_{546} skeleton satisfies Def3.1(a)(b), local I_546/b=273,
  q-order coprimality, 2,3-smooth 41-free F, and exact mod41 G=H=GL2.
- **E2 (CFTH/TC/arch failure): OPEN.** If the finite donor/TC/arch inputs fail
  for every actual C, the b=273 no-go is conditional only. No such failure is
  proved.
- **Complete C existence: NOT CONSTRUCTED.** The skeleton is source-level, not
  a fully explicit complete C.

Thus the task-256 b=273 no-go cannot be escaped by E1 on Def3.1(c)/target
grounds. The decisive conditional remains: **if an admissible complete C with
b=273 and CFTH/TC/arch exists, P6 is false in both B branches with margin
>8800.** The only honest escape is E2 (or the absence of a complete C, which is
E1 but not proved).

## 7. Status

- Short natural-language theorem/proof/construction; no Lean/Project edits.
- Source-level b=273 skeleton constructed; exact mod41 image computed;
  Def3.1(c)/target no exclusion; E1 not proved; E2 open.
- No arbitrary curve/data; E_{546} is the standard j-line curve at j=1/p^{546}.
- target_accepted=false; P6 still open/unconditional.
