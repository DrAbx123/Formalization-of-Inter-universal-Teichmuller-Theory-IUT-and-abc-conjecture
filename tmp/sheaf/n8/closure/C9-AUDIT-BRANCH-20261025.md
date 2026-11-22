# C9 audit: reconciliation of task-153 UNDETERMINED and task-155 conditional B=O_K

Task: task-160. Date: 2026-10-25. Auditor: transport.
Stage: read-only natural-language reconciliation. No Lean/Project edits.
Only this file written.

Inputs:

| file | lines | SHA256 |
|---|---:|---|
| C9-MODP-GENERATOR-20261025.md (task-153) | 345 | 8232226E983D95C4495864B7491A864750BF730B03611BC27FC5B5E25D39507C |
| C9-MODP-CERTIFICATE-20261025.md (task-155) | 249 | E5056D524DA94683E5B6BA765EA0AEAF8B23C03D96814F02B49CB47496CC9E95 |
| C9-SYMPLECTIC-SOURCE-20261025.md (task-147 correction) | 313 | 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70 |
| C9-IND1-GLOBAL-20261025.md (task-149 correction) | 531 | 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8 |

## 1. Verdict

branch_reconciliation = NO CONTRADICTION, TWO DIFFERENT CONDITIONAL
STATEMENTS; task-155's headline B=O_K is a conditional subgroup theorem, not
the full barGamma theorem.

- task-153 is correctly labelled UNDETERMINED for the full actual finite image
  barGamma. It proves the exact criterion and shows trace plus Sp data alone do
  not determine l.
- task-155 proves an actual trace computation and a conditional statement for
  the corrected subgroup H=Phi^{-1}(Sp_40(Z_p)). If the inferred trace basis
  alignment holds, U=l, and H fixes l.
- But H fixing l is not the same as the full barGamma fixing l. task-155's
  conclusion B=O_K follows only for the subgroup H (or after adding the
  hypothesis barGamma(l)=l / barGamma=H on I/J). As stated for the full actual
  finite image, it is an overclaim.
- task-155's b=3 numerical branch values are conditional local formula values;
  under task-149 they are not target-containment theorems and must carry the
  TC-A..TC-H plus TC-S conditions.

So the two files do not conflict mathematically. They conflict in wording:
task-153 says full barGamma unknown; task-155 says B=O_K under an alignment
assumption, but its proof only covers the Sp subgroup, not the full barGamma.

## 2. Exact correct conditional theorem

Let K/Q_p be the task-155 local field:

    p=12301, e=41, K=Q_p(pi), pi^41=p,
    O_K=Z_p[pi], J=m=pi O_K, I=p^{-1}J,
    l=O_K/J = span(1) in I/J.

Let H=Phi^{-1}(Sp_40(Z_p)) be the corrected actual closed subgroup of
Out(G_K), with Phi(H)=Sp_40(Z_p). Under the 2026 basis after the inferred
2025/2026 alignment, let

    k_+ = U direct-sum W, U fixed, W standard Sp_40,
    I/J = Ubar direct-sum Wbar,
    l = span(1,v),  v in F_p^40,

normalized so the Ubar coordinate is 1 whenever the trace is nonzero. Let
barGamma be the full finite image of the actual Aut(G_K) additive action on
I/J, and B the closed span of barGamma(O_K) as in C9-TAME.

The exact statements are:

(A) If v != 0, then H generates all of I/J from l; hence B=I regardless of
    any further elements of barGamma. This direction is stable under passing
    from H to barGamma.

(B) If v = 0, then H fixes l. The full branch is:
      B = O_K  iff  barGamma fixes l;
      B = I    iff  some gamma in barGamma moves l
                    (then its image has nonzero Wbar component and the
                     H orbit generates all of I/J).
    Thus v=0 plus H fixing l does NOT by itself imply B=O_K for the full
    barGamma; one needs the additional condition barGamma(l)=l (or
    barGamma=H on I/J, or all actual generators preserve l).

(C) task-155's conditional theorem is the special case:

      v=0 AND barGamma(l)=l  =>  B=O_K.

    It is valid as a subgroup/conditional theorem. It is not the unconditional
    full-barGamma theorem.

The missing datum is therefore exactly:

    (i) the actual vector v (equivalently the coordinates lambda of 1 in the
        actual 2026 symplectic basis, or the basis-alignment matrix), and
    (ii) the full finite image barGamma on I/J (or a proof that every actual
        generator fixes l).

task-153 states this correctly as UNDETERMINED. task-155 computes v only under
the natural trace alignment (v=0) and checks H fixes l, but does not supply
(ii).

## 3. The trace computation in task-155

The trace table is actual and correct in the pi-power model:

    I/J = pi^{-40}O_K / pi O_K,
    basis (e_0,e_{-40},...,e_{-1}), e_a=pi^a,
    Tr(e_0)=41, Tr(e_{-k})=0 for 1<=k<=40.

Proof: Tr(pi^a)=0 for 1<=a<=40 in the tame totally ramified extension, and

    pi^{-k}=u^{-1} pi^{e-k}/p

gives Tr(pi^{-k})=u^{-1}p^{-1}Tr(pi^{e-k})=0.

Since p=12301 does not divide 41, the field-trace line of I/J is l=span(e_0).
This is a correct exact local computation.

What it does NOT prove:

- It does not identify the field-trace line l with the 2026 U-line. That
  identification is the inferred basis-alignment convention from task-147.
- It does not compute the W-coordinate v in the 2026 basis.
- It does not compute the full barGamma action.

task-155 itself states these caveats in Sections 3 and 6. The audit confirms
the caveats are not cosmetic: without them the word "B=O_K" is not justified.

## 4. Finite model e=5,p=5 in task-153

The model is consistent with task-155, not in conflict:

- e=5,p=5 is explicitly a finite representation model, not the actual
  p>e+1 C9 field.
- U=e_1, W=F_5^4, l_fix=U orbit span 1, l_move=<e_1+e_2> orbit span 5.
- Both lines have nonzero trace, so trace plus Sp data do not decide v.
- task-155's actual trace table gives v=0 only after the alignment convention;
  the model shows why a general trace theorem cannot supply that convention.

The model does not disprove task-155's conditional statement; it shows why the
statement must be conditional. The model also does not prove the actual branch
is B=I; it only proves insufficiency of the source data used in TAME section 2.

## 5. Overclaims / errors to classify

task-155:

1. MAIN OVERCLAIM: "Under this conditional certificate ... B=O_K; B=I does
   NOT occur." The proof only shows H=Phi^{-1}(Sp) fixes l when v=0. It does
   not show the full barGamma fixes l. Status: valid as a conditional subgroup
   theorem, overstated as a full-barGamma statement. Correction: add
   "barGamma(l)=l" or "barGamma=H on I/J" as an explicit hypothesis.

2. LOCAL VALUE USE: "the b=3 local value is the B=O_K branch -411/41, not
   B=I 9/41." These values are local formula evaluations under TAME section 5.
   task-149 says equations (11)-(14) are not a target proof and TAME section 5
   must not be used as actual. The values are conditional/local only; any
   target-containment use needs TC-A..TC-H plus TC-S. Status: conditional
   computation, not a theorem; warning stands.

3. The finite matrix check in task-155 is correct for its stated conditional
   purpose: A=I-E_{1,21} is symplectic and fixes l=(1,0,...,0). It does not
   compute v and does not test B=I; task-155 labels this, so no error.

4. The trace table itself is actual; no overclaim there. The phrase "trace
   line is exactly l" is correct for the field trace; the subsequent
   identification U=l is the inferred convention and is flagged by task-155.

task-153:

1. No overclaim found. It explicitly labels UNDETERMINED, distinguishes the
   corrected H donor from the full barGamma, and states the missing basis/
   lambda/full-image data.
2. Its e=5,p=5 model violates p>e+1 for the actual C9 type, but it is clearly
   labelled a finite model, not an actual K. No error.
3. Its statement "trace plus Sp data alone are insufficient" is correct and
   compatible with task-155's conditional cert.

task-147 and task-149 corrections:

- task-147: donor H=Phi^{-1}(Sp), rho not homomorphism, boundary-word
  substitution not actual source, basis alignment inferred, trace target
  Tr_{K/K^{d=1}}. Both audits honor these.
- task-149: TAME section 5 equations (11)-(14) not target proof; full Ind1 is
  procession automorphism group; no F(Hull) subset H_C from ring isomorphism;
  TC-A..TC-H plus TC-S needed. The branch audit does not claim any target
  containment.

## 6. Current branch status

Unconditional source-only status:

    source_generator_status = UNDETERMINED.

Because the actual v and full barGamma are not computed.

Conditional subgroup status:

    If the 2025/2026 trace alignment holds (U=trace line, v=0),
    then H=Phi^{-1}(Sp_40) fixes l.
    If additionally barGamma(l)=l, then B=O_K.
    If v!=0, then B=I.
    If v=0 but some actual generator moves l, then B=I.

Conditional local formula status:

    Under the same trace alignment, task-155's local B=O_K branch value is
    -411/41 (local source-side value). This is conditional and is not a
    target-containment theorem. The B=I value 9/41 is not selected by the
    trace alignment; it would require v!=0 or a moving full barGamma.

No branch is finalized for the full actual barGamma.

## 7. Exact missing proof obligations

To close the B branch for the actual K:

1. Basis/line coordinate:
   prove the 2025 trace basis equals the 2026 symplectic basis (or compute the
   alignment matrix), and compute the W-coordinate v of O_K/J.
   This is the exact gap between task-155's trace line and the 2026 U-line.

2. Full finite image:
   compute barGamma on I/J, or prove every actual generator fixes l when v=0,
   or provide an actual gamma moving l when applicable. H alone is not enough
   for B=O_K.

3. Conditional finite criterion:
   v=0 and barGamma(l)=l -> B=O_K;
   v!=0 -> B=I;
   v=0 and some gamma moves l -> B=I.
   This is the exact correct theorem; no additional branch is missing.

4. Downstream target:
   even after B is known, all target-container use needs TC-A..TC-H plus
   TC-S, and TAME section 5 values are not a target proof. No h_C<=Q_C or
   F(Hull) subset H_C is claimed.

## 8. Final classification

- task-153: CORRECT; UNDETERMINED remains the full-barGamma status.
- task-155: PARTIALLY CORRECT / CONDITIONALLY VALID. Trace computation and
  finite check are correct. The headline B=O_K is valid only for the H subgroup
  or after adding barGamma(l)=l; the full-barGamma conclusion and the b=3
  branch-value use are conditional. Classify as conditional subgroup theorem,
  not a proof of the full B branch.
- Reconciliation: no mathematical conflict; conditional vs undetermined.
- target_accepted=false.
