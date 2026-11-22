# C9 audit: natural-language underdetermination theorem

Task: task-223. Audit of C9-NL-UNDERDETERMINATION-20261025.md.
Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language verification only.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Input

- C9-NL-UNDERDETERMINATION-20261025.md, 302 lines,
  SHA256 aafe2bc84d93debacf06298b38d7b20694b6a04a0adbf262ddb87d366e4d0582.
- Context: C9-Y1-TRACE (E35), C9-HAFULL-CORRECTED-ATTACK (E26),
  C9-HAFULL-LITE, C9-PRINCIPAL-FILTRATION (P false).

## 1. Verdict

The **main underdetermination conclusion survives**, and Model A is valid.
Model B is valid as an abstract coordinate model **provided one adds an
explicit surjectivity hypothesis on the recorded action**:

    (R6) the recorded H maps onto Sp_{40}(Z_p) in the y-basis,
         i.e. every A in Sp_{40}(Z_p) occurs as alpha_+|W.

Without (R6), the proof of B=I does **not** follow from (R1)-(R5): the statement
"A runs over Sp_{40}(Z_p)" is used in the B=I orbit argument but is not among
the listed recorded data. For the actual corrected donor
H=Phi^{-1}(Sp_{40}(Z_p)) this surjectivity is true (Phi(H)=Sp by construction),
so the theorem is valid for that H; as a pure theorem about (R1)-(R5) it is
incomplete. The theorem should state R6 explicitly.

Three further points need correction/clarification; none destroys the
underdetermination conclusion:

1. **Identity element.** H contains id, so B always contains
   alpha_id(O_K)=O_K, and the identity contributes the line l=O_K/J modulo J.
   This does NOT force B=O_K: B is the Z_p-span of the union, and nonintegral
   images from other alpha can enlarge O_K to I. Model B's B=I is compatible
   with B containing O_K. The proof of B=I should use the identity contribution
   explicitly, not only the class of u0.

2. **u0 is in I, not outside I.** The task wording "u0 notin I?" is false.
   In Model B, u0=1+pi/p. With pi/p=u pi^{-40} and
   I=p^{-1}J=pi^{1-e}O_K=pi^{-40}O_K, both 1 and pi/p lie in I, so u0 in I.
   Its valuation is
       v_p(u0) = min(0, 1/41-1) = -40/41,
   so u0 notin O_K, but u0 in I. The model uses exactly u0 in I setminus O_K.

3. **a(alpha) membership.** For all A,
       a(alpha_A)=u0+A w0=1+pi/p-A(pi/p) in I,
   because 1 in I and pi/p, A(pi/p) in p^{-1}L subset I. For A=-I,
       a=1+2pi/p in I, v_p(a)=-40/41, so a notin O_K.
   Thus H_A-full fails in Model B; a is still in I.

4. **B is a span over all H, not only generators.** The theorem defines B using
   the union over recorded H. The identity element must be included (it is in
   H). If one instead used only a generating set, the orbit/span argument for
   p^{-1}L would need separate proof; the theorem should not silently switch.
   Its B=I proof also has a small gap: it asserts that the classes
   A(p^{-1}pi) occur in B, whereas B directly contains differences
   a_A-1=z-Az. The gap is repairable (see Section 4).

## 2. Model A audit

Model A:

    y1=p, y_i=pi^{i-1} (2<=i<=41).
    Tr(y1)=41p, c=1/p, u0=1, w0=0.
    a(alpha_A)=1 for every A; H_A-full true; B=O_K.

Checks:

- y1..y41 is a Q_p-basis; W=Qp-span(pi,...,pi^40); Tr(y1)=41p nonzero in
  pZ_p; y_i in J; J=Zp-span(y1..y41).
- 1=c y1 exactly.
- alpha_+(O_K)=Zp 1+J=O_K for all A; H_A-full true; B=O_K.
- identity element is consistent (it is one of the A).

Model A is a valid abstract coordinate model for (R1)-(R5) (and R6).

## 3. Model B audit: H_A-full failure

Model B:

    y1=p+pi, y_i=pi^{i-1} (2<=i<=41).
    Tr(y1)=41p, c=1/p,
    u0=1+pi/p, w0=-pi/p.
    a(alpha_A)=1+pi/p-A(pi/p).

Checks:

- y1..y41 is a Q_p-basis; y2..y41 basis of W; y_i in J; Tr(y1)=41p
  nonzero; J=Zp-span(y1..y41) because p=y1-y2.
- u0 in U=<y1> and u0=c y1; w0=1-u0 in W.
- u0 in I setminus O_K; w0 in W cap I.
- For A=-I,
      a=1+2 pi/p, v_p=-40/41, a notin O_K.
  Hence alpha_{-I}(O_K)=Zp a+J is not O_K; H_A-full false.
- For every A, a in I: 1 in I, pi/p in p^{-1}L subset I,
  A(pi/p) in p^{-1}L subset I. Thus alpha_A(O_K)=Zp a+J subset I.

This part is valid: H_A-full false, all alpha(O_K) subset I, identity included.

## 4. Model B audit: B=I and the identity element

The theorem's B is

    B=closed Z_p-span union_{alpha in H} alpha_+(O_K),
    alpha_+(O_K)=Zp a(alpha)+J.

### 4.1 Identity contributes O_K, but does not force B=O_K

Since id in H, alpha_id(O_K)=O_K subset B; modulo J, B contains the line
l=O_K/J. This is compatible with B=I: O_K subset I, and I is larger than O_K.
The identity element cannot be used to conclude B=O_K unless all other
alpha(O_K) are also O_K; Model B has A=-I nonintegral, so no such conclusion.

### 4.2 B subset I

For all A, a(alpha_A) in I and J subset I; hence alpha_A(O_K) subset I for every
alpha in H. Since I is closed, B subset I. Valid.

### 4.3 B/J is all of I/J

We fill the small gap in the theorem's proof.

- Identity: O_K subset B; its class mod J is l, the 1-dimensional line.
- A=-I: a_{-I}=1+2z in B with z=pi/p; 1 in B (identity);
  since 2 is a unit in Z_p, z=(a_{-I}-1)/2 in B.
- For each A: a_A=1+z-Az in B; since 1,z,a_A in B, Az in B.
  Hence p^{-1} A pi=Az in B for every A in Sp_{40}(Z_p).
- The set {A pi : A in Sp_{40}(Z_p)} is the orbit of the primitive vector pi
  in L=Zp-span(pi,...,pi^40); it generates L as a Z_p-module (Sp acts
  transitively on primitive vectors and the orbit contains a basis;
  equivalently the mod-p orbit is all nonzero vectors). Therefore
  p^{-1}L subset B.
- Modulo J, p^{-1}L has the W-part basis
      p^{-1}pi, p^{-1}pi^2, ..., p^{-1}pi^40
  whose classes are pi^{-40},...,pi^{-1}; these span the W-part of I/J.
- With the identity's l and this W-part, B/J=I/J. Since J subset B subset I,
  B=I.

Thus B=I is valid **under the surjectivity R6** used to let A run over all
Sp_{40}(Z_p). The theorem's written proof uses that surjectivity but does not
list it; add R6.

### 4.4 If R6 is absent

If the recorded H is an arbitrary subgroup acting by A in Sp but not surjecting
onto Sp, the orbit {A pi} may span a proper subspace of L; then B/J may be
smaller than I/J and B=I is not proved. The same applies if H is replaced by a
generating set with a smaller orbit. Therefore the theorem as a statement about
(R1)-(R5) only is incomplete; for the actual H=Phi^{-1}(Sp) it is valid.

## 5. Theorem 6 and Corollary 7

Theorem 6 (H_A-full => B=O_K) is valid:

- H_A-full means a(alpha) in O_K setminus J for every alpha (Lemma 1);
- then alpha(O_K)=O_K for every alpha;
- union is O_K; closed span is O_K; B=O_K.

Corollary 7 (B != O_K => H_A-full fails) is the contrapositive and is valid.

The invalid W subset J shortcut is correctly rejected; Lemma 2 uses
O_K=Z_p 1 direct-sum (J cap W), which is correct.

## 6. Underdetermination survives

The two models satisfy (R1)-(R5) and (R6 if H=preimage donor):

    Model A: H_A-full true, B=O_K.
    Model B: H_A-full false, B=I.

They differ in y1/u0/w0/C and have opposite outcomes. The identity element is
present in both and does not collapse them. Therefore the recorded structural
data do not determine H_A-full or B; actual F(x_i)/Tr/c/C are missing input.
The conclusion of the theorem is correct; the proof needs the R6 clarification
and the small B/J spanning detail.

## 7. Classification

| item | verdict |
|---|---|
| Model A H_A true/B=O_K | VALID |
| Model B H_A false | VALID |
| u0=1+pi/p in I (not outside I) | TRUE; v_p=-40/41; u0 notin O_K |
| a(alpha)=1+pi/p-A(pi/p) in I | VALID |
| a(-I)=1+2pi/p notin O_K | VALID |
| B contains O_K via identity, but B=O_K not forced | TRUE; B=I compatible |
| B subset I | VALID |
| B=I proof | VALID under R6 (H onto Sp); otherwise incomplete |
| B definition over all H vs generators | all H required; identity included |
| theorem as stated with (R1)-(R5) only | CONDITIONAL/INCOMPLETE; add R6 |
| underdetermination conclusion | SURVIVES |
| H_A-full => B=O_K | VALID |
| B!=O_K => H_A-full fails | VALID |

## 8. Conclusion

The natural-language underdetermination theorem is **substantively correct**
for the actual corrected donor H=Phi^{-1}(Sp_{40}(Z_p)), whose image is all of
Sp. Its Model B B=I is not invalidated by the identity element; B contains O_K
and can equal I because other alpha images add p^{-1}L. The task's suspicion
that u0 notin I is wrong: u0 in I setminus O_K. a(alpha) lies in I for all
alpha and fails integrality at A=-I.

The theorem needs three fixes before being stated as a pure (R1)-(R5) theorem:

1. add R6: H maps onto Sp_{40}(Z_p) (or H is the preimage donor);
2. state that B uses all of H including id;
3. fill the B/J spanning argument via z=(a_{-I}-1)/2 and Az=1+z-a_A.

With these, Model A/B and the underdetermination conclusion are valid.
No arbitrary coordinates; no Lean/kernel closure; P6 open.

## 9. Status

- Natural-language audit only; no Lean/Project edits.
- Theorem/proof adjudicated: valid for donor H with R6; incomplete as pure
  (R1)-(R5). Model B B=I and u0 membership corrected.
- target_accepted=false.
