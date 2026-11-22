# C9 adversarial review of the C1 toolkit

Task ID: task-460 / C9-C1-TOOL-ADVERSARIAL-20261025. Reviewer: primespine. Date: 2026-10-25.
Object: tmp/sheaf/n8/closure/C9-C1-NEW-TOOLS-20261025.md (90 lines).
Scope: independent adversarial review; no rewriting; no Lean/Project edits; no mixed/E3; only this file written.

## 0. Verdict

**REJECT the C1 toolkit as a proof strategy.** The toolkit is a collection of unproved conjectures, not source consequences. Tool I's rationalization/invertibility is not defined from the source; Tools II-III assume density/closedness of admissible structures that are not established; Tool IV assumes essentially the C1 output membership; Tool V is a conditional theorem whose hypotheses already contain the desired conclusion. No tool supplies a source-valid C1 derivation.

Option A is correctly identified as circular for an independent proof; but the new tools do not avoid the circularity, they relocate it into new conjectures.

## 1. Tool I (rationalized LGP): REJECT

Problems:

1. **C_l is not a Q-vector space.** The volume container/log-shell is a p-adic/adelic object with a monoid action, not an abelian group with a canonical Z-module structure. `C_l tensor_Z Q` is not source-defined.
2. **LGP is not known to be Q-linear/invertible.** The source action of LGP/N on log-shells is a construction algorithm, not a linear endomorphism. If LGP is a nonunit (as the file itself says in §6), rationalization does not automatically make multiplication by it bijective. The claim 'L is bijective on the rationalization' is an extra hypothesis, not a source theorem.
3. **S^Q is outside the small container.** The exact rational preimage `L^{-1}(S_q)` lies in `C_l^Q`; it is not a subset of `C_s`. Restricting `L_s: C_s -> C_l^Q` does not give an inverse on C_s, and its image need not reach `[S_q]`.
4. **No source for the map L_s.** The LGP action's domain/image on `C_s` is exactly one of the unresolved D1 issues; Tool I assumes it.

## 2. Tool II (admissible density): REJECT

The Density conjecture says Adm (measurable, N-compatible, adelic integral structures) is dense in measurable subsets of C_s in some topology. Problems:

1. **No source/theorem.** Density of admissible integral structures is not in LANA/IUT; it is a new conjecture.
2. **Admissibility is not a dense condition.** N-compatibility/adelicity are rigid constraints; admissible sets may be sparse or closed with empty interior. No reason density should hold.
3. **Approximation does not give the target.** A sequence `[L_s(S_n)] -> [S_q]` in Rss only shows S_q is in the closure of the image. To get S with equality one needs the target in the image and the image closed; neither is proved.
4. **Topology unspecified.** 'a topology for which L_s and the volume-class map are continuous' is not defined; different topologies change the conjecture.

## 3. Tool III (compactness exactification): REJECT

Problems:

1. **C_s compactness is not enough.** Even if C_s is compact, Adm need not be closed; a limit of admissible S_n may fail N-compatibility/adelicity/integrality.
2. **Convergence of S_n does not imply convergence of [L_s(S_n)] unless L_s is continuous; continuity is assumed, not proved.**
3. **Target closure is still needed.** Compactness gives a limit S in the closure of Adm, but does not prove `[L_s(S)]=[S_q]` unless `[S_q]` is already in the closure/image; that is the missing approximation theorem, not a compactness consequence.
4. **The limit may not be admissible.** The conclusion 'S in Adm' assumes Adm closed; no proof.

## 4. Tool IV (output-volume interval): REJECT; circular

The Output interval conjecture says O_vol is a closed interval in (-inf,h] and contains values arbitrarily close to Q from above (or Q is a limit point forced by Ind1/2/3). Problems:

1. **No source.** O_vol is not known to be an interval, closed, or to have Q as a limit point. The multiradial output set is subject to Ind1/2/3; there is no theorem that its log-volume set is an interval.
2. **Essentially C1.** If Q is in O_vol, that is C1. If Q is only a limit point, closedness is needed to conclude Q in O_vol; the conjecture bundles the desired conclusion.
3. **Ind1/2/3 may not force Q as a limit.** Ind3 is upper semi-compatibility, not an approximation to the q-pilot value; no source continuity/limit theorem.

## 5. Tool V (C1-toolkit theorem): REJECT as a C1 proof

The theorem assumes:

(i) L_s continuous;
(ii) Adm dense and closed;
(iii) volume classes continuous and Rss Hausdorff;
(iv) O_vol closed and Q in its closure.

Then it concludes C1. This is a valid **conditional** implication, but every hypothesis is unproved. In particular (iv) is essentially the output-membership problem, and (ii) combines two incompatible requirements (dense and closed) without a source topology. The theorem does not reduce C1; it packages the gaps.

## 6. Circularity/missing source summary

- Tool II/III: target `[S_q]` must be in the closure/image of `L_s`; this is the desired compatibility, not derived.
- Tool IV: Q in O_vol/closure is C1 itself; closedness is an extra unproved property.
- Tool V: hypotheses (ii)/(iv) contain the conclusion.
- Tool I: rationalized LGP invertibility is a new algebraic hypothesis with no source; LGP is a construction algorithm/nonunit, not a Q-linear automorphism.

No LANA/IUT theorem supports density, compactness exactification, or output interval.

## 7. Accept/reject table

| tool | verdict | exact reason |
|---|---|---|
| Tool I rationalized LGP | REJECT | no Q-vector structure; LGP nonunit/not Q-linear; S^Q outside C_s |
| Tool II admissible density | REJECT | new unsourced conjecture; admissibility rigid; approximation not equality |
| Tool III compactness | REJECT | Adm closedness/continuity/target closure unproved; limit may not be admissible |
| Tool IV output interval | REJECT | unsourced; Q in O_vol is C1; closedness/limit unproved |
| Tool V theorem | REJECT as C1 proof | conditional only; hypotheses include conclusion; no source |
| Option A source lemma | ACCEPT only as source-conditional | xi-f is source assertion; not independent proof |

## 8. Final review verdict

**REJECT the C1 toolkit.** It replaces the exact compatibility with unsourced density/compactness/interval conjectures; the output interval and admissible density steps are circular or assume C1. No tool provides a rigorous C1 derivation. C1 remains open. No mixed/E3; no Lean.

target_accepted=false.
