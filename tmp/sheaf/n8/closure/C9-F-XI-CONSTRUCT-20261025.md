# C9 explicit Kondo F(x_i)/y1 via Kummer theory

Task: task-219. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language/exact local research only.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Inputs

- C9-Y1-TRACE-20261025.md (task-217 source obstruction),
  SHA256 a33ebdb8d0d0551b1391cf3069c71b8cf3255d8b56f20f96513c7f33e22f425c.
- C9-HAFULL-COORDINATES-20261025.md,
  SHA256 06299f26383af7da73dc8bb844f2fef7c939d486bd922cec5e1785f0df0cbbf4.
- C9-PRINCIPAL-FILTRATION-P-20261025.md (P false),
  SHA256 f125420f44405b360a289cdf1787c6c4f979d122eb6e65072639df1b6e160599.
- Kondo 2025 local snapshot,
  sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f.
- Kondo 2026 local snapshot,
  sources/Kondo-2605.25428v2.html,
  SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86.

Binding: y_i=F(x_i) is a Q_p-basis of K_+; W=ker Tr=<y2,...,y_d>;
y_i in J=m and [y_i]=0 in I/J (E16); full Out does not preserve the upper
ramification/principal filtration (task-209 P false). H_A-full remains open.

## 1. Goal and verdict

Goal: use Kummer theory for K=Q_p(pi), pi^41=p u, e=41, p=12301, to extract
explicit Kondo F(x_i), in particular y1=F(x1), then compute Tr(y1),
c=41/Tr(y1), and C, and decide w0=1-c y1 and H_A-full_H/B_H.

Verdict: **Kummer theory supplies no source-determined extraction.** The
Kummer pairing determines finite-order (41-torsion) classes and the uniformizer/
root-of-unity Kummer structure, but Kondo's x_i are pro-p generators of wild
inertia, and F(x_i) is a p-adic log of a pro-p unit under local reciprocity.
No frozen source identifies x_i or F(x_i) with a Kummer dual basis, normalizes
the trace Tr(y1), or fixes C. The task-217 underdetermination remains:
the recorded Kondo/Kummer data do not determine y1,Tr(y1),c,C,u0,w0, and
H_A-full_H/B_H are undetermined. No arbitrary coordinate is used.

## 2. Kummer setup

Let K=Q_p(pi), e=41, p=12301, pi^41=p u, u in Z_p^times, f=1. Since
p=1 mod 41, mu_41 subset Q_p, and K/Q_p is a cyclic degree-41 Kummer extension
in the tame totally ramified class. Write

    O_K=Z_p[pi], m=(pi), J=log(O_K^times)=m, I=p^{-1}J.           (2.1)

Kummer theory over K (or over Q_p with mu_41) gives:

- the uniformizer class [pi] in K^times/(K^times)^41, equivalently the cyclic
  extension K/Q_p;
- a perfect pairing between K^times/(K^times)^41 and G_K on mu_41;
- a dual basis of finite-order Kummer classes, but only after choosing
  generators and a basis of the F_41-vector space K^times/(K^times)^41.

These are finite-order mod-41 data. They are not the pro-p logarithms
F(x_i)=log(unit part of x_i under local reciprocity). The Kummer pairing
describes 41-torsion extensions, whereas F(x_i) lands in the Q_p-vector space
K_+ through the p-adic log of units in 1+m; the two are different levels.

## 3. What Kummer theory fixes and what it does not

Kummer theory fixes:

- the uniformizer class pi^41=p u and the root-of-unity mu_41;
- a noncanonical dual Kummer basis of finite-order classes;
- the fact that the degree-41 extension is cyclic tame.

It does NOT fix:

1. the actual pro-p wild inertia generators x_1,...,x_d of G_K used by the
   Jordan-Wingberg presentation;
2. their unit images under local reciprocity, equivalently the p-adic logs
   y_i=F(x_i);
3. the trace value Tr(y1), beyond Tr(y1) in pZ_p and nonzero;
4. the trace normalization of the y-basis, hence c=41/Tr(y1);
5. the coordinates of 1 in the y-basis, hence u0,w0;
6. the coordinates of the y_i in an O_K-basis, hence C;
7. the trace pairing x,y -> Tr(xy); the Kummer pairing is not this trace
   pairing and does not determine it.

The Kondo existence theorem selects some JW generators x_i with relations; it
does not identify them with a Kummer dual basis. A Kummer basis is canonical
only up to the choice of a basis of K^times/(K^times)^41; different choices
change the finite-order classes and their logs. No frozen source supplies the
choice that would match Kondo's x_i.

## 4. Attempted Kummer extraction and its failure

A natural attempt is:

1. Choose a Kummer basis of K^times/(K^times)^41, e.g. from pi and a basis of
   units.
2. Take reciprocal images in G_K and their p-adic log-unit values to define
   candidates for y_i.
3. Compute Tr(y1), c, C from those candidates.

This fails at step 2: local reciprocity on the pro-p part is not the Kummer
pairing. The Kummer pairing is a finite-order pairing with mu_41; the elements
x_i are pro-p (wild inertia), and their F-images are p-adic logarithms in J.
The reciprocal image of a Kummer class is only defined up to an element of
G_K^41, and the log of its unit part depends on the pro-p lift, not just the
finite-order class. No source theorem says that Kondo's x_i are the chosen
Kummer lifts.

Even at the level of units, the trace theorem only gives

    W=ker Tr=<y2,...,y_d>,  Tr(y1) in pZ_p, Tr(y1) != 0,           (4.1)

not the value Tr(y1). The Kummer basis normalizes products/powers of units, not
the trace of their p-adic logarithms. Consequently Kummer data alone cannot
compute c=41/Tr(y1), u0=c y1, or w0=1-u0.

## 5. Explicit structural calculations (conditional forms)

If an external source supplied y1, the exact formulas are:

    1=u0+w0, u0=c y1, c=41/Tr(y1), w0=1-c y1,
    a(alpha)=alpha_+(1)=u0+A w0,
    H_A-full_H <=> u0+A w0 in O_K for all A in Sp_40(Z_p).     (5.1)

For the two structural models already recorded in task-217:

- y1=p: Tr(y1)=41p, c=1/p, u0=1, w0=0, H_A-full_H true,
  B_H=O_K.
- y1=p+pi: Tr(y1)=41p, c=1/p, u0=1+pi/p, w0=-pi/p; for A=-I,
  a=1+2pi/p notin O_K, so H_A-full_H false and B_H is not O_K.
- y1=2p: Tr(y1)=82p, c=1/(2p), u0=1,w0=0,H_A true.

Kummer theory does not select among these models. They satisfy the recorded
structural axioms (Q_p basis, W=kerTr, y_i in J, J=Z_p-span of the y-basis,
Sp diag(1,A), D fixes y1); no source theorem fixes the actual F(x_i) values
that would choose one. The models are not claimed to be actual Kondo tuples;
they demonstrate the insufficiency of the recorded axioms.

## 6. Exact source obstruction

The frozen source determines only the following structural facts:

- existence of a JW basis y1,...,y_d=F(x1),...,F(x_d);
- W=ker Tr=<y2,...,y_d>;
- y_i in J=m and [y_i]=0 in I/J;
- Sp embedding diag(1,A) in the y-basis;
- D fixes y1 in k_+;
- Tr(y1) in pZ_p nonzero.

It does not determine y1,Tr(y1),c,C,u0,w0. Kummer theory adds only finite-order
Kummer classes and a noncanonical dual basis; it does not identify these with
the pro-p JW generators or their p-adic log-unit values. Therefore:

- no source-determined y1 or Tr(y1);
- no source-determined c or C;
- H_A-full_H and B_H=O_K/B_H=I are UNDETERMINED;
- full H_A-full/B branch open.
This is a source obstruction, not an actual counterexample.

## 7. Classification

| item | status |
|---|---|
| K=Q_p(pi), e=41, pi^41=p u, mu_41 subset Q_p | ACTUAL |
| Kummer pairing / finite-order dual basis | ACTUAL/STANDARD |
| Kummer basis determines Kondo x_i/F(x_i) | FALSE/NOT SUPPLIED |
| F(x_i)=log(unit) in J; W=kerTr | ACTUAL paper-level |
| Tr(y1) in pZ_p nonzero | ACTUAL structural |
| Tr(y1), c=41/Tr(y1), C | NOT DETERMINED |
| u0=c y1, w0=1-u0, H_A-full criterion | EXACT FORMULA conditional on y1 |
| H_A-full_H/B_H source decision | UNDETERMINED |
| full H_A-full/B branch | OPEN |
| Kummer extraction of explicit F(x_i) | FAILS: source obstruction |

## 8. Conclusion

Kummer theory does not extract explicit Kondo F(x_i)/y1. The Kummer pairing is
finite-order (41-torsion) and noncanonical, while the Kondo y_i are p-adic logs
of pro-p unit parts of JW generators; no frozen source identifies the two,
normalizes Tr(y1), or fixes C. The exact conditional formulas for c,u0,w0 and
H_A-full are recorded, and the task-217 coordinate models show opposite
H_A/B outcomes. Hence y1/Tr(y1)/c/C remain source-undetermined, H_A-full_H and
B_H are undetermined, and no target/B-branch conclusion follows.

No complete C, no target containment, no global inequality. P6 open;
target_accepted=false.

## 9. Status

- Natural-language/exact local research only; no Lean/Project edits.
- Kummer extraction attempted and obstructed; source underdetermination
  confirmed.
- No arbitrary coordinates, no fabricated closure.
