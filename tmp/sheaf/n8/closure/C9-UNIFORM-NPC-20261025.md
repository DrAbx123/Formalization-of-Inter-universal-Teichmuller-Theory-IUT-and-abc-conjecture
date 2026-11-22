# C9 uniform NPC/M3: no extra possible-image class beyond R_B+arch

Task: task-320. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits; no mixed/E3 profiles.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-SATURATION-MAXIMALITY-20261025.md (task-300), 108 lines,
  SHA256 daa9cd08c20b06594c6622e1806fdce22831baa275e7bdd4f98c1597591bc5ac.
- C9-TARGET-EXTRA-NEW-20261025.md (task-285), 130 lines,
  SHA256 a5356db164e2cbf62f8382dd5a9574ed587a73aff1bdc90efa15974ed8668dfd.
- C9-RA-SUBSET-RB-20261025.md (task-298), 147 lines,
  SHA256 b89dc64ccbe6d6b564f629947b7cba0346cab8fa2ba58703ed5ab7b56e3ecc4e.
- C9-S2-UPPER-INDEPENDENT-20261025.md (task-302), 136 lines,
  SHA256 33fc2c9fdb703d2eba3da2dd3176d5772190e11466d4a6464c95897793ea2ef7.
- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.

Scope: fixed F_mod=Q uniform target; one selected bad p and selected good
places; no mixed rho and no E3 profile change.

## 1. Definition

NPC/M3 (uniform): every possible image of the full uniform target
Ind1/Ind2/Ind3/BPS/Theta family lies in the hull of the TAME branch-row
family plus the arch component. Equivalently, the target hull H_C has no
positive-volume complement beyond

    R_B + arch,   R_B=Hull(L_B),  L_B=p^{s-r+1}J^{tensor r}.         (1.1)

If NPC holds, the saturation upper U follows:

    h_C <= H_B+h_inf.                                                 (1.2)

## 2. Verdict

**NPC/M3 is NOT proved in the frozen source, and it is not refuted by a
source-valid countermodel.** The exact situation:

- TAME section6 supplies only (M1): for the fixed all-bad subfamily, the local
  lattices are L_A (B=O_K) and L_B (B=I), and L_A subset L_B (task-298);
  there is no third local lattice in that subfamily.
- TAME does NOT supply (M3): it explicitly says its classification is only for
  the listed actual subfamily, not an upper bound for the entire C output
  family. Full Ind1/Ind2/Ind3/BPS/Theta may contain additional possible images.
- TC-A..H/TC-S supply lower containment/transport/volume preservation, not an
  exhaustion theorem. TC-B says H_C is the hull of the full possible-image
  family; that is the opposite direction from NPC.
- Task-285 shows no **constructed** positive extra region beyond R_B exists in
  the frozen corpus, but absence of a constructed extra is not a proof of NPC.
  It is a conditional no-new-region statement, not target exhaustion.

Thus NPC is a genuine missing source theorem, not a consequence of TAME/TC.
The conditional implication NPC + (M1/M2) => U is valid. Under U, b=273 gives
the conditional counterexample with margin 8821.54 (both B branches). Without
NPC, the uniform upper side remains open.

## 3. Conditional theorem

Theorem 3.1 (NPC => U). Assume:

(M1) TAME section6 local saturation: every local row image is in the hull of
     L_A or L_B, and L_A subset L_B;
(M2) target row/Theta normalization: H_C is the row/Theta weighted hull of
     these branch hulls; TC-C/D/E/G preserve row weights and normalized
     volumes; the arch component is bounded by h_inf;
(M3) NPC: there is no positive-volume possible-image class beyond the branch
     row hulls plus arch.

Then

    h_C <= max(H_A,H_B)+h_inf = H_B+h_inf.                           (3.1)

Proof. By (M1), every local row image lies in R_A or R_B; by task-298
R_A subset R_B. By (M2), the target normalized volume is at most the row/
Theta weighted average of the branch values, hence at most
max(H_A,H_B). By (M3), no extra positive-volume class contributes. Add the
arch term. QED.

Corollary 3.2 (b=273 under NPC). With H_B=(-38736/41)logp and
A_proc=11.5log pi:

    h_C <= H_B+A_proc,
    F=Q_C-h_C >= D_B-A_proc
      = 8821.538890... >0.                                        (3.2)

This is a conditional P6 counterexample in both B branches; it depends
crucially on (M3).

## 4. Why TAME/TC do not prove NPC

1. TAME section6 is a local classification of the listed all-bad subfamily.
   Its own text disclaims an upper bound for the whole C output family.
2. TC-B is a lower/saturation containment: source possible images are
   contained in H_C. It does not say H_C is contained in the source branch
   rows.
3. TC-C/D/E/G preserve volumes/weights/labels; they do not exclude an
   additional possible-image class with its own positive volume.
4. Ind1 is a procession automorphism group; factor permutations/processions
   reorder rows but do not by themselves exhaust all full Ind1/Ind2/Ind3/
   BPS/Theta possible images.
5. Task-285's no-new-region theorem is conditional on its assumptions (i)-(iii)
   and is a volume/no-construction statement, not an exhaustion of all source
   possible images. It cannot be used as (M3).

## 5. Logical countermodel to derivability of NPC

The following is a TC-valid **logical** model, not a source-constructed
possible image:

Start with the two branch row families R_A,R_B (R_A subset R_B) and add one
extra possible-image class E_extra with normalized volume epsilon>0 and
disjoint support in a target row. Define H_C to be the hull of the union.
Let the transport/TC maps act volume-preservingly on the original source
regions (identity on E_extra). Then:

- all TC-A..H/TC-S containment/preservation semantics can be satisfied;
- H_C contains R_B plus E_extra, so
      h_C >= H_B+h_inf+epsilon > H_B+h_inf;
- NPC and U fail by epsilon.

No source-valid E_extra is constructed; this countermodel only shows that
TC/TAME alone cannot imply NPC. It does not refute NPC for the actual source;
it refutes the claim that NPC follows from the current TC/local-saturation
data.

## 6. What would prove NPC

A genuine uniform NPC theorem would need one of:

- (N1) an exhaustion theorem: every full Ind1/Ind2/Ind3/BPS/Theta target
  possible image is contained in the hull of the TAME branch rows plus arch;
- (N2) a direct upper bound h_C<=H_B+h_inf for every uniform target C;
- (N3) a target-volume equality/TC-upper theorem showing H_C has no positive
  complement beyond R_B+arch;
- (N4) a classification of all uniform source possible images finer than TAME
  section6 and a proof that no extra class exists.

None is in the frozen corpus. Task-285 does not supply (N1)-(N4); it supplies
only conditional no-new-region/volume under its assumptions.

## 7. Classification

| item | status |
|---|---|
| TAME section6 local L_A/L_B saturation | CONDITIONAL/INFERRED |
| R_A subset R_B | PROVED (task-298) |
| NPC/M3 uniform | NOT PROVED |
| TAME/TC imply NPC | FALSE; logical countermodel E_extra |
| source-valid NPC countermodel | NONE constructed |
| NPC => U | PROVED conditional |
| U => b=273 F>=8821 | PROVED conditional on NPC/U |
| uniform U unconditional | NOT OBTAINED |
| mixed/E3 used | NO (excluded) |

## 8. Conclusion

Uniform NPC/M3 is not proved by TAME section6, TC, task-285, or R_A subset R_B.
TAME gives only the local branch classification; TC gives lower containment and
volume preservation; task-285 is conditional and does not exhaust the full
possible-image family. The conditional chain NPC => U => b=273 counterexample
with margin 8821.54 is valid, but its first premise is the exact missing source
theorem. A TC-valid logical countermodel with an extra possible-image class
shows no proof can derive NPC from TC/TAME alone; no source-valid extra class is
constructed. Thus the uniform upper side remains open, with NPC/M3 as the
decisive missing input. No mixed/E3 profile is used.

No arbitrary source region; no Lean/kernel closure; target_accepted=false;
P6 conditional on NPC, otherwise open.

## 9. Status

- Short natural-language theorem/obstruction only; no Lean/Project edits.
- Uniform NPC/M3 status, conditional U theorem, logical countermodel and exact
  missing theorem recorded.
- target_accepted=false.

## 10. Critical check: average H_B vs max over rows

Row j=1 of the B=I family has

    s_1=floor(b/41),
    nu_B,1/log p = -s_1+1-2/41.

For b=3: s_1=0, nu_B,1=39/41 log p ~0.951, while H_B=9/41 log p ~0.219.
For b=273: s_1=6, nu_B,1=(-6+1-2/41)log p=(-207/41)log p ~-5.049, while
H_B=(-38736/41)log p ~-944.78. In both cases nu_B,1 > H_B.

Does this refute U? Only under a **geometric-union/max** interpretation of the
target hull. The C9 target readout is not that.

TAME section6 and the task-274/task-285 row construction define R_B as a
**row/Theta weighted procession family**

    R_B = union_j T(R_B,j),   uniform row/Theta weight 1/m, m=20,   (10.1)

and the normalized target height is the weighted procession readout

    h_C = sum_j w_j nu_j + h_inf,   w_j=1/m,  sum_j w_j=1.          (10.2)

The rows R_B,j live at different tensor orders r=j+1 and are transported into
different procession levels; they are not subsets of one common measure space
whose geometric union would have volume >= max_j nu_j. The readout (10.2) is a
convex combination, as task-285 states: any mixture is a convex combination of
row heights, and the uniform profile has weights 1/m. Thus containing row j=1
contributes weight 1/m to h_C; it does not force h_C>=nu_B,1. The average
H_B=(1/m)sum_j nu_B,j is the correct finite readout, and U with H_B is not
refuted by nu_B,1>H_B.

If one instead replaces the C9 weighted readout by the geometric measure of a
set-theoretic union (max over rows), then:

- U_uniform fails exactly at row j=1: h_C>=nu_B,1>H_B, so h_C<=H_B+h_inf is
  false for both b=3 and b=273.
- For b=273, Q_p=-(273/41)log p ~-6.659 and nu_B,1~-5.049, so
  F=Q_p-h_C <= -1.610<0; the alleged b=273 counterexample fails in this
  geometric-max corridor (P6 may hold there). The same applies to b=3.
- But this is a different target normalization (geometric union/measure)
  than the C9 procession weighted readout (10.2); it changes the target
  object and is not permitted for the original uniform P6.

Therefore, under the actual C9/TAME weighted readout, row j=1 does **not**
give an exact uniform counterexample to U; H_B remains the finite average.
The max interpretation is a target-normalization change, and if adopted it
would refute U and remove the b=273 counterexample, not support it.

Consequence: the task-320 conclusion is unchanged. U/NPC is not refuted by
row j=1 under the source readout; NPC/M3 remains the missing theorem. No
uniform counterexample to U and no b=273 counterexample follows from the
average-vs-max issue alone.
