# C9 uniform U: independent proof attempt h_C <= H_B + h_inf

Task: task-316 (uniform scope). Owner: qside. Date: 2026-10-25.
Short natural-language theorem/proof and exact obstruction; no mixed/E3
profiles; no Lean/Project/target edits; only this file written.

## 0. Scope correction

Only the fixed uniform F_mod=Q target is used: one selected bad place per
rational p, bad mass rho=1.  The TAME Section 5 mixed bad/good profiles are
E3 profile changes and are not possible images of this target; no mixed
region is inserted here.  This file asks only the uniform question:

    (U)  h_C <= H_B + h_inf,                                    (0.1)

where H_B is the larger uniform B=I finite row value and h_inf is the
archimedean term.  For b=273 this is U273.

The independent proof attempt meets the same missing target-exhaustion
statement as before; U is **not proved** from the frozen uniform source.  The
conditional consequence is exact: U273 gives

    F = Q_C - h_C >= D_B - h_inf >= D_B - A_proc
      = 8821.538890956... > 0,                                  (0.2)

where D_B=(38463/41)log 12301=8834.703284644..., A_proc=11.5 log pi=13.164393687... .
No counterexample is obtained without U.

## 1. Uniform data and signs

p=12301, e=41, F_mod=Q, one selected bad place.

b=3:
    Q_p = -(3/41) log p,
    H_A = -(411/41) log p,
    H_B = (9/41) log p,
    D_3 = Q_p - H_A = (408/41) log p = 93.7149712746...,
    S3 = H_B - Q_p = (12/41) log p = 2.7563226845....

b=273:
    Q_p = -(273/41) log p,
    H_A = -(39156/41) log p,
    H_B = -(38736/41) log p,
    D_A = Q_p - H_A = (38883/41) log p = 8931.174578603...,
    D_B = Q_p - H_B = (38463/41) log p = 8834.703284644....

B_I-zero arch: h_inf=sum_v alpha_v [h_v^ang + log r_v]; IV container gives
only the upper bound h_inf<=A_proc=11.5 log pi=13.164393687... .

## 2. Source lower bound (not U)

TAME Sections 5-6 give the actual uniform B=I row region R_B with

    R_B subset H_C  (conditional on TC-B/source realization),
    h_C >= H_B + h_inf.                                        (2.1)

This is a lower bound for h_C.  It is the opposite direction from U.  In
particular, the C1/CFTH residual formula

    Q_C - h_C <= D_C^Sp - h_inf                                (2.2)

is an upper bound on F=Q_C-h_C, not the lower bound F>=D_C^Sp-h_inf.
Signs must not be reversed (E48).

## 3. Conditional U theorem (valid but hypothesis missing)

Theorem 3.1.  Let C be a uniform complete C.  Suppose the target-hull
exhaustion statement

    (Exh) H_C subset Hull(R_B union arch_region)                (3.1)

holds up to zero normalized volume, and the arch component has normalized
base value h_inf.  Then

    h_C <= H_B + h_inf.                                        (3.2)

Proof.  R_B has normalized finite height H_B; arch has height h_inf; the hull
of R_B union arch has normalized volume at most H_B+h_inf (the row region is
fixed, the arch component is fixed, and normalized log-volume is monotone).
By (Exh), H_C has at most that volume.  QED.

For b=273 under (Exh) and h_inf<=A_proc:

    F = Q_C - h_C >= -(273/41)log p - (H_B + h_inf)
      = D_B - h_inf
      >= D_B - A_proc = 8821.538890956... > 0.                 (3.3)

Thus U273 would make b=273 a P6 counterexample (F>0) with margin
8821.538890956..., conditional on a complete C and (Exh).

## 4. Why the independent uniform proof fails

The source gives the lower inclusion

    R_B subset H_C,                                             (4.1)

but not the upper inclusion (Exh).  The available ingredients are:

1. TAME Section 6 row classification: for the fixed all-bad uniform tuple the
   local source regions are B=O_K and B=I rows; R_A subset R_B is proved.
2. TC-B: H_C is the hull of the full possible-image union, so R_B subset H_C.
3. TC-C/transport: the allowed Ind1/factor permutations/Theta-gluing transport
   the same rows and preserve normalized volume (conditional).
4. Good finite places have normalized height zero in the C9 normalization; the
   arch term is h_inf.

These prove a **row-only** lower envelope, not a global upper envelope.  To get
U one must additionally show that no uniform source-valid possible image/hull
lies outside R_B+arch, and that the hull operation does not enlarge beyond that
envelope.  TAME §6 explicitly classifies a fixed all-bad subfamily, not the
entire target output family; the target container contains R_B but its volume
is not H_B+h_inf.  The IV container gives only

    H_C subset C_C,  h_C <= nu(C_C),                             (4.2)

with nu(C_C) not identified with H_B+h_inf.  Since H_B is a lower row height
and C_C is a containing container, nu(C_C) is generally strictly larger.

The missing statement is exactly target-exhaustion/NPC/M3:

    (NPC/M3) H_C has no positive-volume complement beyond R_B+arch.  (4.3)

Equivalently, (Exh) up to zero normalized volume.  It is not a consequence of
TC-B (which is a lower inclusion), TC-C (which is volume preservation), or the
row classification.  No uniform source-valid extra region is constructed
either; U is neither proved nor refuted from the frozen source.

## 5. Independent verdict / exact obstruction

The uniform U proof does not close.  The exact obstruction is (NPC/M3)/(Exh),
not the finite row arithmetic:

- R_A subset R_B is proved; TAME rows give a lower bound;
- the target hull is a hull of the full possible-image union, and no source
  theorem says that union is contained in R_B+arch;
- the target container is an upper bound by a different (larger) volume, not
  by H_B+h_inf;
- mixed/E3 regions are excluded by the uniform V-section and are not used;
- no source-valid uniform extra region is constructed, so U is not disproved
  either; it is an open target-exhaustion statement.

Consequently the b=273 consequence (3.3) is conditional on U/NPC and a complete
C, not an unconditional counterexample.  Likewise b=3 results remain
conditional; U does not prove P6 for b=3.

## 6. What would prove U

A genuine independent uniform proof would need one of:

1. a global target-exhaustion theorem: every uniform possible image/hull lies
   in R_B+arch up to zero volume (NPC/M3);
2. a direct volume upper bound nu(H_C)<=H_B+h_inf from the actual source
   construction, not from the target container;
3. a sharp row/transport classification covering all uniform possible images,
   including hull closure and all allowed Ind1/Theta-gluing actions.

None is in the frozen source.  Adding one of them as a hypothesis is a new
source theorem, not a consequence of current data.

## 7. Classification

PROVED/ACTUAL:
- uniform finite row values H_A,H_B,Q,D_A,D_B,S3;
- R_A subset R_B (TAME/task-291);
- R_B subset H_C => h_C>=H_B+h_inf (conditional on TC-B/source realization);
- conditional theorem: (Exh) or NPC/M3 => U => b=273 F>=8821.538890956...;
- target container gives only h_C<=nu(C_C).

CONDITIONAL:
- TC-B actual target hull and R_B transport;
- IV arch h_inf<=A_proc;
- complete C and finite/global assembly.

MISSING/OPEN:
- uniform target-exhaustion NPC/M3/(Exh);
- actual H_C/C_BPS/Theta/TC data;
- unconditional U and unconditional b=273 counterexample;
- actual h_inf lower bounds for P6 sign.

No mixed/E3 profile is used.  No arbitrary extra region or volume is chosen.
target_accepted=false; P6 open/conditional.

## 8. Sources

- C9-UPPER-BOUND-20261025.md (U not implied by container; sharpness needed).
- C9-NPC-M3-20261025.md (NPC/M3 exact missing theorem; uniform scope).
- C9-B3-SATURATION-20261025.md (U3/U273 conditional consequences).
- C9-MASTER-V4-20261025.md (uniform signs/status).
- C9-TAME-LOG-DOMAIN-20261025.md Sections 5-6 (row values; fixed all-bad
  subfamily, not global upper).
- C9-MIXED-VOLUME-EXACT-20261025.md and mixed-profile files are not used:
  they are E3 profile-change results and excluded by the uniform V-section.
