# C9 H_A-full coordinates: u0,w0,C for the Kondo U/W basis

Task ID: task-215 / C9-HAFULL-COORDINATES-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact local research only; no Lean/Project edits; no target changes; no arbitrary coordinates; only this file written.

## 0. Inputs and binding facts

- C9-HAFULL-NONFILTRATION-20261025.md (task-214), SHA256 cf0c383170805060768feed0a981484c04204cf9669386fce8dbd0a416efc658.
- C9-AUDIT-UNIT-FILTRATION-20261025.md (task-208), SHA256 8d715581577f057c151cc7023b98f5a896a04121efc32d13b6ebaef21c563e09.
- C9-HAFULL-INTEGRALITY-20261025.md (task-204), SHA256 16523153a35bf386899ac2f36eb6db53c777f7ca704034615646bd84df002929.
- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (task-180), SHA256 7cc2ddd03cfefa97e38049ca1ccb90016e944dece0185f706e42f7f97cd61fd8.
- Kondo 2026 local snapshot, Definition3.2 and preceding paragraph: the U/W basis is the fixed y1,...,y_d basis of k_+, with U=<y1>, W=<y2,...,y_d>; the Sp embedding is diag(1,A).
- Kondo 2025 Theorem E/1.3: for odd d, W=ker Tr_{k/k^{d=1}}; in the tame totally ramified case k^{d=1}=Q_p.

Binding E16: the y_i lie in J=m and vanish in I/J; they are not an I/J basis. The U/W basis is a Q_p-basis of K, not a Z_p-basis of O_K. This file does not confuse the two.

## 1. Exact form of u0,w0 given the y-basis

Let K=Q_p(pi), e=41, p=12301, O_K=Z_p[pi], pi^e=p u, J=m, I=p^{-1}J. The Kondo U/W decomposition is

    K=U direct-sum W,   U=<y1>_{Q_p},   W=<y2,...,y_d>_{Q_p},   d=41,   (1.1)

with W=ker Tr and Tr(y1) nonzero. We write the actual field identity as

    1 = u0 + w0,   u0 in U, w0 in W.                           (1.2)

Because U is one-dimensional and W=ker Tr,

    u0 = c y1,   c = Tr(1)/Tr(y1) = 41/Tr(y1),                 (1.3)
    w0 = 1 - c y1.                                             (1.4)

This is the exact coordinate formula. It is not arbitrary: c is fixed by the trace and Tr(y1). The missing datum is the actual value Tr(y1), equivalently the actual y1=F(x1) in K.

Since y1 in J=m and Tr(J) subset pZ_p, Tr(y1) lies in pZ_p and is nonzero; hence c has v_p(c)<=-1. Both u0 and w0 may be nonintegral vectors; their sum is 1. No integrality of u0,w0 separately follows.

## 2. Exact form of the change-of-basis matrix C

Choose a Z_p-basis B_O=(1,pi,...,pi^40) of O_K (or any other fixed Z_p-basis). Let

    C = ( [y1]_{B_O}, [y2]_{B_O}, ..., [y_d]_{B_O} ) in GL_41(Q_p)   (2.1)

be the change-of-basis matrix from the U/W y-basis to the O_K basis: C maps a y-coordinate column to the corresponding O_K-coordinate column. For a vector v, write [v]_y for its y-coordinate column. Then

    C [u0+A w0]_y in Z_p^{41}   iff   u0+A w0 in O_K.          (2.2)

For alpha in H with alpha_+|U=id and alpha_+|W=A in Sp_{40}(Z_p),

    a(alpha)=alpha_+(1)=u0+A w0.                               (2.3)

Thus H_A-full_H is exactly

    u0 + A w0 in O_K for every A in Sp_{40}(Z_p),               (2.4)

equivalently the first column of the O_K-basis matrix of diag(1,A) is integral for all A.

## 3. What the sources do and do not determine

The Kondo papers determine:

- the existence of the fixed JW basis y1,...,y_d of k_+ (Kondo 2026 Theorem1.2/preceding text);
- W=ker Tr=<y2,...,y_d> for odd d (Kondo 2025 Theorem E/1.3);
- the embedding diag(1,A) of Sp_{2g}(Z_p) in this basis (Kondo 2026 Definition3.2);
- the basis elements y_i=F(x_i) are p-adic logs of units, hence y_i in J=m.

They do **not** determine:

1. the actual values y_i=F(x_i) in K, beyond the basis and trace-kernel properties;
2. the trace value Tr(y1), hence c=41/Tr(y1);
3. the coordinates of 1 in the y-basis, hence u0,w0;
4. the matrix Y of y_i relative to a Z_p-basis of O_K, hence C;
5. actual preimage matrices of alpha in H on O_K.

The trace theorem gives the kernel W and the nonzero-ness of Tr on U, but not the value Tr(y1) or the pairing Tr(xy); the trace pairing uses multiplication, which is not part of the Q_p-linear reconstruction. The JW generators x_i are not accompanied by explicit p-adic unit values in the frozen sources. Therefore u0,w0,C cannot be numerically computed from the current corpus without additional source input.

## 4. Conditional tests and exact obstruction

The integrality test is

    u0 + A w0 in O_K.                                         (4.1)

Possible outcomes:

1. If w0=0, then 1=u0 in U and a(alpha)=1 for all A; H_A-full_H holds and B_H=O_K. The condition w0=0 is equivalent to 1 in U=<y1>, i.e., y1 a Q_p multiple of 1; no source proves or disproves this.
2. If w0 is nonzero but the y-basis is integral for O_K (C integral and 1 coordinates integral), then (4.1) may hold for all A; H_A-full_H follows.
3. If w0 has a denominator in the O_K basis and A can move it outside O_K, then some a(alpha) is nonintegral; H_A-full_H fails and the B branch is not O_K. This is a possible branch, not an actual counterexample without C.

The exact obstruction is the triple (y1, Tr(y1), C) or equivalently (u0,w0,C). Without it, neither H_A-full_H nor B_H=O_K/B_H=I is decided. No filtration assumption is used; the non-filtration alpha exist by Kondo 2025 Theorem A, but they do not supply the coordinates.

## 5. B branch status

Under the exact data:

- If (4.1) holds for all A, B_H=O_K.
- If all a(alpha) lie in I minus O_K and the H-orbit generates I/J, B_H=I.
- If some a(alpha) is outside I, the O_K/I branch dichotomy is not defined.

The current sources do not decide which case holds. The full B branch for Out remains open; task-204's all-Out B=O_K/B=I exclusion is withdrawn (task-208).

## 6. Actual / conditional / missing

Actual:

- U=<y1>, W=<y2,...,y_d>, W=ker Tr, y_i in J; 1=c y1+w0 with c=41/Tr(y1); a(alpha)=u0+A w0.
- H is infinite, Aut(k) finite, so non-filtration alpha in H exist; they do not preserve U^n.

Conditional:

- Any integrality/H_A-full_H/B_H statement depends on y1,Tr(y1),C; these are not supplied.

Missing:

- Actual y_i values, Tr(y1), u0,w0, C, explicit alpha matrices; complete C, TC-A..TC-H/TC-S, archimedean h_inf; global h_C>=Q_C.

Withdrawn:

- Task-204 filtration-based a(alpha) in O_K; task-195/200 W/trace construction is independent but does not supply C; no unconditional B=O_K/B=I.

## 7. Next executable steps

1. Extract from the actual Kondo reconstruction the values y_i=F(x_i) for the fixed JW generators (or their coords in a chosen O_K basis). This is the first missing computation.
2. Compute Tr(y1) and c=41/Tr(y1), then u0=c y1, w0=1-u0.
3. Build Y and C; test u0+A w0 for generators A of Sp_{40}(Z_p) (e.g. transvections).
4. If a nonintegral a(alpha) is found, determine whether it lies in IO_K and whether the orbit spans I/J; this decides B_H=I versus undefined.
5. If all are integral, prove (4.1) for all A; then H_A-full_H and B_H=O_K follow.

Status: stage1 natural-language/exact local arithmetic only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6/ABC not proved.
