# C9 saturation maximality: proof attempt for U3/U273, or countermodel

Task: task-300 (C9-SATURATION-MAXIMALITY-20261025). Owner: logdescent. Date: 2026-10-25. Decisive U attack; only this file written; no Lean/Project/target/other-owner edits; no arbitrary source region. P6 unproved; target_accepted=false.

Inputs: C9-B3-SATURATION-20261025.md (task-293); C9-TARGET-EXTRA-NEW (task-285); C9-TARGET-POSITIVE (task-271); C9-BI-REGION (task-274); TAME §6; C9-TC-EQUALITY; C9-P6-NOGO.

Convention E47: F=Q_C-h_C; P6 is h_C>=Q_C, F<=0. U3/U273 is the saturation upper

    h_C <= max(H_A,H_B)+h_inf.                                       (0.1)

## 0. Verdict

U3/U273 is NOT proved from TAME §6 maximality alone. TAME §6 gives a local saturation theorem for the fixed all-bad source subfamily (only B=O_K/B=I local lattices), but the target H_C is the hull of the full Ind1/Ind2/Ind3 possible-image family, and no source theorem gives the reverse inclusion/exhaustion (no positive target complement) needed for (0.1).

A conditional proof of U is available if one adds the missing **no-positive-complement (NPC)/target-exhaustion** hypothesis. Under that hypothesis, U follows and the b=273 consequence is

    h_C <= H_B+A_proc = -8884.245232030... < Q_p=-62.706341073...,
    F=Q_p-h_C >= 8821.538890956... >0,                                  (0.2)

so b=273 is a P6 counterexample in both B branches with margin at least 8821.54.

No actual/source TC-valid countermodel to U is constructed; the only countermodel is the abstract TC-valid model with an extra possible-image region, which shows TC containment/preservation does not imply U. The exact obstruction is the missing source NPC theorem, not a TAME local-lattice defect.

## 1. Proof attempt from TAME §6

TAME §6 classifies the actual subfamily obtained from the Gaussian integral region, the full per-factor Gamma action, and factor permutations for a fixed all-bad r-tuple:

    B=O_K: L_A=sum_i p^s pi_i D_r,
    B=I:   L_B=p^{s-r+1}J^{tensor r},                                (1.1)

with row/T17 heights and the statement that the action is saturated in this finite local type (no third lattice). For the uniform profile, the row/Theta weights are fixed and the normalized local branch values are

    H_A=(-411/41)logp,  H_B=(9/41)logp  (b=3);
    H_A=(-39156/41)logp, H_B=(-38736/41)logp (b=273).                (1.2)

Attempted proof of U:
(M1) local maximality: for each row and fixed all-bad tuple, every source finite possible image lies in the hull of the B=O_K or B=I branch lattice; no third local lattice.
(M2) target normalization: the target hull is the row/Theta weighted hull of these branch hulls; TC-D/E/G preserve row weights and q/BPS labels; the fixed-gluing transport is volume-preserving (TC-C).
(M3) target exhaustion/NPC: the full Ind1/Ind2/Ind3 possible-image family has no positive-volume complement beyond the branch row hulls (no extra target possible-image class).
Then, per row, the hull volume is at most the branch value; the branch is global for the fixed C (not independently mixable per row beyond the uniform row weights); the weighted average is at most max(H_A,H_B); adding the arch component gives (0.1). This proves U conditionally on (M1)-(M3).

What TAME §6 supplies is (M1), and only for the fixed all-bad subfamily; it is an inferred source consequence (task-147), not a Kondo theorem. It does NOT supply (M3): TAME §6 says the lattice action is saturated within its finite field type, not that the full target possible-image family (full Ind1 poly-morphisms, Ind2/Ind3 log/Kummer branches, BPS/Theta-gluing) has no additional positive-volume region. The target H_C is larger than the selected subfamily by TC-B; TC-B is a lower inclusion, not an upper/exhaustion.

Thus the proof stops at (M3). This is the exact obstruction.

## 2. Why TC does not imply U

TC-A..H/TC-S give:
- TC-A: source procession identity;
- TC-B: H_C is the hull of the full possible-image family (a larger family; lower inclusion for H_C);
- TC-C: normalized-volume preservation/isometry;
- TC-D/E/G: row/place/profile/q-class preservation;
- TC-H: Ism/Ind2 bookkeeping;
- TC-S: corrected donor.

None says the full possible-image family equals the selected branch-row family. In fact TC-B's saturation direction is the opposite of U: a larger possible-image family gives a larger H_C. The C9-TC-EQUALITY countermodel makes this explicit: start with the branch row families and add an extra possible-image region E_extra of normalized volume epsilon>0, with disjoint support in a target row; all containment/preservation semantics of TC-A..H can still be satisfied (F remains volume-preserving on its source region; the extra region is an additional possible image), but

    h_C >= max(H_A,H_B)+h_inf+epsilon,
so U fails by epsilon.                                                  (2.1)

This is a **logical/TC-valid countermodel**, not an actual complete C and not a source-constructed region; E_extra is not supplied by the source. It proves that TC-A..H/TC-S alone cannot derive U; an additional source exhaustion theorem is required. No arbitrary source region is claimed.

## 3. Conditional theorem and b=273 consequence

Theorem 3.1 (conditional saturation U).
Assume (M1) TAME §6 local saturation, (M2) target row/Theta normalization and volume-preserving transport, and (M3) no positive target complement. Then

    h_C <= max(H_A,H_B)+h_inf.                                       (3.1)

Proof: (M1) puts every local image in one of the branch hulls; (M2) gives the weighted row/Theta average; (M3) excludes extra positive-volume target classes; add h_inf. QED.

Corollary 3.2 (b=273). Under U273 and the b=273 finite values,
    max(H_A,H_B)=H_B=(-38736/41)logp=-8897.409625717...,
    h_C <= H_B+A_proc=-8884.245232030... < Q_p=-62.706341073...,
    F=Q_p-h_C >= 8821.538890956... >0.                                (3.2)

Thus b=273 is a P6 counterexample in both B=O_K and B=I branches, with margin at least 8821.54. This is a conditional repair of the upper side of the task-256 no-go.

Corollary 3.3 (b=3 split). Under U3, with H_B=2.067242013... and S_3=2.756322684...:
- h_inf<-S_3 -> h_C<Q_p -> counterexample;
- h_inf=-S_3 -> h_C<=Q_p, P6 iff equality; otherwise counterexample;
- h_inf>-S_3 -> upper undecided; with B=I target region lower h_C>=H_B+h_inf>Q_p -> P6, otherwise undetermined.                            (3.3)

## 4. Exact obstruction and status

Proved conditional:
- (M1)+(M2)+(M3) -> U.
- U -> b=273 counterexample F>=8821.538890956; b=3 h_inf split.

Proved obstruction:
- TC-A..H/TC-S do not imply U; logical countermodel (E_extra) satisfies TC semantics and violates U by epsilon.
- TAME §6 gives only local saturated branch classification (M1), not NPC (M3) for the full target possible-image family.
- No source-constructed actual extra region exists in the current corpus (task-285); but absence of a constructed region is not a proof of NPC.

Missing:
- source theorem NPC/M3: every Ind1/Ind2/Ind3/BPS/Theta target possible image lies in the hull of the TAME branch rows; equivalently H_C has no positive-volume complement beyond max(H_A,H_B)+h_inf.
- actual TC/gluing/arch and complete C.

Status of b=273:
- If U is proved (or accepted as source theorem), b=273 is a conditional P6 counterexample with margin 8821.54; then P6 would be false for an admissible complete C (if one exists).
- Without U, C1 only gives h_C>=H_A+h_inf and F<=D-h_inf; it does not prove F>0. The b=273 no-go remains conditional on U/NPC, not on C1/CFTH/TC/arch alone.

## 5. Conclusion

TAME §6 maximality is a local saturation statement (M1), not the global target exhaustion (M3) required for U. The proof of U stops exactly at the missing NPC theorem; TC alone permits a logical extra-region countermodel but no source-valid countermodel is known. If NPC/U is supplied, b=273 becomes a P6 counterexample with margin 8821.54 and b=3 has the exact h_inf split. Otherwise U remains the decisive missing source theorem; no arbitrary region is used.

Only C9-SATURATION-MAXIMALITY-20261025.md written. No Lean/Project edits. target_accepted=false; P6 conditional on U, otherwise open.
