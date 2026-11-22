# C9 new target extra region beyond the B=I sibling

Task: task-285 (C9-TARGET-EXTRA-NEW-20261025). Owner: logdescent. Date: 2026-10-25. New angle/short theorem/proof attempt; only this file written; no Lean/Project/target/other-owner edits; no arbitrary enlargement. P6 unproved; target_accepted=false.

Inputs: C9-TARGET-POSITIVE-20261025.md (task-271); C9-BI-REGION-CONSTRUCTION-20261025.md (task-274); C9-TAME §6 (B=O_K/B=I saturation); C9-GLOBAL-ASSEMBLY (T15b/T15c/T16); C9-FIXED-GLUING-SWAP; C9-IND1-GLOBAL (TC-A..H/TC-S).

Convention E47: F=Q_C-h_C; P6 is h_C>=Q_C, i.e. F<=0. The B=I sibling region is the conditional extra of task-274, with local height (9/41)logp.

## 0. Verdict

No canonical target extra region of the required b=273 volume is constructed from full Ind1/procession/factor permutations/BPS/Theta-gluing beyond the B=I sibling.

The exact obstruction is the source saturation theorem of TAME §6, conditional on the corrected finite donor/TC data:
- Within a fixed all-bad r-tuple and the allowed Gaussian integral region, the full source orbit is already saturated: the only local lattice branches are B=O_K and B=I. There is no third lattice.
- Factor permutations/processions reorder the same row lattices; the normalized row/Theta weights are fixed by the profile and preserved by TC-D/E/G. They do not create a new volume class beyond the B=O_K/B=I row hulls.
- BPS/Theta-gluing and TC-C preserve the q/BPS labels and normalized volumes; they transport the region, not enlarge its normalized volume.
- The archimedean container adds at most A_proc=13.164.

Thus the largest source-conditional extra beyond the selected B=O_K hull is the B=I branch difference
    Delta_B=(420/41)log12301=96.471293959...,
and with the arch cap a total of at most
    Delta_B+A_proc=109.635687646...
For b=273 the smallest required extra (at h_inf=A_proc) is
    R_req,min=D_273-A_proc=8918.010184916...,
so the source-conditional gap is at least
    8808.374497... >0.
No new source region closes it.

For b=3, Delta_B alone exceeds D_3=93.714971275 by S_3=2.756322685, which is exactly the task-271 conditional rescue (with h_inf>=-S_3). The new angle cannot improve b=273.

## 1. Required extra and the known B=I bound

Write H_sel for the selected B=O_K finite local hull and h_inf for the arch component. P6 needs an extra target region R with

    nu(R) >= R_req := Q_C-(H_sel+h_inf)=D_C-h_inf,
    D_C := Q_C-H_sel.                                                (1.1)

For b=273:
    Q_p=(-273/41)logp, H_A=(-39156/41)logp, D_273=(38883/41)logp=8931.174578603...;
    H_B=(-38736/41)logp, Delta_B=H_B-H_A=(420/41)logp=96.471293959...;
    A_proc=13.164393687... .                                         (1.2)

For b=3:
    D_3=(408/41)logp=93.714971275..., Delta_B=96.471293959...,
    Delta_B-D_3=S_3=(12/41)logp=2.756322685... .                     (1.3)

The B=I sibling region of task-274 supplies Delta_B conditionally. The new task is to find a region beyond it; the answer below shows the source-saturation obstruction.

## 2. Full Ind1/procession/factor permutations: saturation, not a new lattice

TAME §6 classifies the actual subfamily obtained by the Gaussian integral region, the full per-factor Gamma action, and factor permutations. The exact classification is:

    B=O_K: L_A=sum_i p^s pi_i D_r,
    B=I:   L_B=p^{s-r+1}J^{tensor r},                               (2.1)

and the corresponding row heights are (T17a/T17b). The source conclusion is that the action is saturated within this finite local type; repeating same-type automorphisms does not produce a third lattice. This is the inferred source consequence (task-147 labels it inferred, not a Kondo theorem), but it is the only saturation theorem available; without it there is no constructed alternative either.

Consequences:
- Factor permutations permute the row lattices; under TC-C's volume-preserving transport they do not change their normalized volumes.
- The uniform row/Theta weights are fixed by the profile (rho=1, weights sum1) and preserved by TC-D/E/G. The normalized local height of any mixture is a convex combination of row B=O_K/B=I heights; per-row B=I-A difference is 40j/41 logp>=0, so the maximal mixture is all-B=I, giving Delta_B (the B=I sibling). No mixture exceeds it.
- Full Ind1 is a procession automorphism group, not a finite label translation; its orbit can permute/relabel rows and factors, but not create a larger normalized-volume lattice class in the saturated local type. A claim of a new numeric volume would require a new saturation theorem, not a permutation.
- The target container IV bounds the arch direction; it does not add a finite region.

Thus beyond the B=I sibling, the full Ind1/procession/factor-permutation data do not supply an additional quantified region. This is the first exact obstruction.

## 3. BPS/Theta-gluing: transport, not enlargement

The fixed-gluing common terminal transport T sends the B=I row hulls into the same target container, preserving row j, q/BPS labels, Theta-gluing, and target column/normalization (TC-A/TC-D/TC-E/TC-S, conditional). It is the transport used in task-274 to build R_B. It does not:
- increase the normalized volume of a region (TC-C is an isometry/preservation, not a dilation);
- add a new q-pilot/BPS row (TC-E preserves q class; changing it is E3, a different profile);
- create a second region at the same row with independent volume (the possible-image family is the orbit of the same source row; the hull volume is the row hull, not a sum over arbitrary images).

Therefore BPS/Theta-gluing confirms the B=I transport but adds no numeric extra beyond Delta_B. A new BPS/Theta region of volume ~8808 would be an arbitrary enlargement unless a source construction of a new q/BPS class is given; none is.

## 4. Archimedean container: cap, not region

IV gives h_inf<=A_proc=13.164393687... . This is an upper bound on the arch component; it is not an additional arch region. Even adding A_proc to the B=I difference gives only 109.635687646..., far below the b=273 required 8918.010 minimum. If h_inf is less than A_proc, R_req is larger, making the gap worse. No arch construction can supply ~8808 (task-240).

## 5. Obstruction theorem

Theorem 5.1 (source-conditional no-new-region for b=273).
Assume:
(i) the corrected finite donor/saturation classification TAME §6 holds (only B=O_K/B=I local branches);
(ii) target normalized row/Theta weights and q/BPS/gluing labels are preserved by TC-A/TC-D/TC-E/TC-G/TC-S;
(iii) the target possible-image family is generated by the fixed-glueing transport of the saturated source rows (no new q/BPS class).
Then any canonical target extra region R beyond the selected B=O_K hull has normalized volume at most
    nu(R) <= Delta_B = (420/41)logp = 96.471293959...
plus the arch cap A_proc in the overall comparison. Therefore for b=273,
    nu(R) <= Delta_B+A_proc =109.635687646... < R_req,min=8918.010184916...,
so no such R reaches P6. The gap is at least 8808.374497....

Proof. By (i)/(ii), row lattice classes are B=O_K/B=I; normalized heights are convex combinations of row heights; maximal extra is all-B=I, Delta_B. Theta/gluing/BPS transport preserves volume (iii), and arch cap contributes at most A_proc. The numerical comparison is (1.2). QED.

The theorem is source-conditional: it uses the C9 saturation classification (inferred) and TC preservation. If one rejects the saturation classification, no alternative constructed region is available either; the construction side still has no candidate. The theorem does not claim an absolute mathematical impossibility of some unknown possible image; it proves no source region exists in the available saturation model.

## 6. What would be needed for a new angle

To construct a region beyond B=I with volume ~8808, one would need one of:
(A) a new local lattice class beyond B=O_K/B=I (new source theorem; not available);
(B) a row/Theta weight change concentrating mass on a high-j row (changes profile/target, E3; forbidden for fixed C);
(C) a new q/BPS/Theta class with independently computed normalized volume (source construction missing; assigning it would be arbitrary);
(D) a target container larger than IV in the finite direction (TC/IV failure, E2; not a P6 proof inside target);
(E) an archimedean region of volume~8808 (impossible under IV, task-240).
All are outside the fixed b=273 target. No arbitrary enlargement is used.

For b=3, (B) is not needed: the B=I sibling plus arch condition already gives the conditional rescue; the new obstruction is specific to the size of the b=273 deficit.

## 7. Proved / conditional / missing

Proved conditional:
- Source saturation classification B=O_K/B=I; factor permutations/processions preserve row weights/volumes; Theta/gluing transport is volume-preserving; arch cap A_proc.
- B=I sibling extra Delta_B=96.471293959..., b-independent; b=3 rescue condition; b=273 total known extra 109.635687646... < 8918.010 min required; gap 8808.374497....
- No new source region beyond B=I is constructed.

Conditional:
- TAME §6 saturation and CFTH/TC-A..H/TC-S;
- B=I actual realization (task-274 missing source object);
- actual arch h_inf and complete C.

Missing/obstruction:
- new lattice/q/BPS/Theta class or weight change (would change target/profile);
- actual target saturation including B=I and full Ind1 beyond row permutations;
- complete C/TC/arch.

## 8. Conclusion

Beyond the B=I sibling Delta_B=96.47, the full Ind1/procession/factor permutations/BPS/Theta-gluing do not supply a new target volume class: they permute/transport the same saturated row hulls and preserve normalized weights/volumes. The b=273 requirement R_req~8918 is short by at least 8808 after the maximum known B=I+arch extra. This is an exact source-conditional obstruction, not an arbitrary enlargement. The only conditional rescue remains b=3 with Delta_B and h_inf>=-S_3; b=273 cannot be rescued by this construction.

Only C9-TARGET-EXTRA-NEW-20261025.md written. No Lean/Project edits. target_accepted=false; P6 open/conditional.
