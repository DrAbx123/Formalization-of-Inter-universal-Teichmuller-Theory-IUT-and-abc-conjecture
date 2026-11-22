# C9 P6-true E1: independent complete-C impossibility for b=273

Task: task-352 (C9-P6TRUE-E1-COMPLETE-C-20261025). Owner: logdescent. Date: 2026-10-25. Independent E1 attack; uniform scope only; no mixed/E3; only this file written; no Lean/Project/target/other-owner edits; no arbitrary. P6 unproved; target_accepted=false.

Inputs: C9-B273-CONSTRUCTION (task-257); C9-B273-COMPLETE-C (task-258); C9-B273-BPS-FSEM (task-329); C9-B273-COMPLETE-BPS; C9-E2-COMPLETE-C; C9-ALT-E-COMPLETION; IUT I Def3.1.

Convention E47: F=Q_C-h_C; P6 h_C>=Q_C, F<=0. Uniform profile F_mod=Q, rho=1, all selected factors bad; no mixed.

## 0. Verdict

E1 (no admissible complete C with b=273) is NOT proved. An independent global impossibility argument is not available from the frozen source. The b=273 E_546 skeleton passes every Def3.1 clause that can be checked at the source-skeleton level, and no source condition bounds b, excludes q-order273, or contradicts mod41 full image.

A concrete complete C is also NOT constructed. The exact obstruction is the missing concrete global BPS/Theta-pilot/0-column/target/TC/CFTH/arch assembly, not a contradiction. Thus:
- E1: OPEN (no impossibility proof).
- Complete C: NOT CONSTRUCTED.
- P6-true via E1: NOT established.

No arbitrary representative is chosen to fill the gaps.

## 1. What E1 would need

E1 is: no admissible complete C with b=273 exists. To prove it, one must derive a contradiction from the source-defining conditions of a complete C, not from missing construction data. The clauses are IUT I Def3.1(a)-(f) plus the target/BPS/Theta/CFTH/TC normalization.

For the E_546 candidate:
- (a) F contains i and full E[6]: F0=Q(i,E[6]), [F0:Q] divides 1152=2^7*3^2, i in F0.
- (b) XF once-punctured E_546; stable reduction after F_sem; field of moduli Q; F/F_mod Galois degree prime to41; full E[2]/E[3] over F.
- (c) l=41; E[41] full; K=F(E[41]); q-order b=273 coprime to41; mod41 image G=H=GL2(F41) exact; local I_546.
- (d) C_K=[X_K/E[41]] type (1,41-tors)^pm; C_F K-core.
- (e) V section over Vbad={p}; local type at p; other bad M-primes semistabilized.
- (f) epsilon origin/canonical cusp.
All pass at source-skeleton level (tasks 257/258). No source restriction bounds b=273; 41 does not divide 273 or 546; p>e+1; qhat=pi^273v; mod41 full. There is no arithmetic/local contradiction.

The only missing objects are concrete/source-global:
- concrete finite-place BPS representative/global BPS label/gluing (task-329 constructs only the full poly-isomorphism class);
- archimedean mono-theta/theta data and BPS gluing (E_546 complex theta values not determined by E_546[41]);
- Theta-pilot 0-column/zero-label splitting/target column/fixed q-volume class;
- explicit C_F/C_K/V/epsilon equations and 41-division coordinates;
- CFTH finite branch, TC-A..H/TC-S, actual target hull H_C and arch h_inf.
These are missing data, not statements that no data can exist. Choosing representatives arbitrarily is forbidden.

## 2. Attempted E1 routes and their failure

(1) Arithmetic/local obstruction: fails. Def3.1(a)-(c) data exist; q-order273 coprime41; e=41, f=1; mod41 GL2; no bound on b.
(2) Field-degree obstruction: fails. F is a real number field, [F:Q] 2,3-smooth/41-free; K=F(E[41]) is finite Galois. There is no requirement that [K:F] be prime to41 (K is not F_mod/F), and no contradiction.
(3) Stable reduction: E_546/F is stable after F_sem at p/M/2,3; no obstruction.
(4) BPS/Theta existence: task-329 constructs the finite-place BPS/Theta package up to full poly-isomorphism from E_546/F_sem/mod41/K. A poly-isomorphism class is the source object; the absence of a chosen representative is not an impossibility. The global concrete environment/arch data are missing, but no theorem says they cannot exist.
(5) Target/TC: TC-A..H/TC-S are conditions to be satisfied, not proven impossible. Task-307/324: NPC/M3 is not proved, but also not refuted; no contradiction.
(6) Archimedean: IV gives only an upper container; no lower bound contradicts b=273. h_inf is missing, not impossible.
(7) p-adic Mahler-Manin: j=1/p^546 rational; q is p-adic transcendental; no contradiction with E_546 existence. q=p^6 was impossible (task-191), but b=273 uses q=p^546+... and is actual.
(8) q-order/quantization: qhat=pi^273v, b=273, 41∤273; no residue/order obstruction. TAME log-domain allows b=273.

No route yields a contradiction.

## 3. Attempted construction: where it stops

Starting from E_546:
- E_546/Q, F0=Q(i,E[6]), F_sem, F=F0F_sem, K=F(E[41]), X_K, C_K/C_F/V/epsilon skeleton are constructed at source level.
- Task-329 constructs the finite-place BPS/F^{⊩▶×mu} label/gluing package and finite-place Theta-pilot 0-column **up to full poly-isomorphism**.
- Missing concrete data (task-329 O1-O5):
  (O1) a concrete representative of the finite-place BPS poly-isomorphism class;
  (O2) archimedean mono-theta/theta data and BPS gluing;
  (O3) zero-label splitting/target column/fixed q-volume class;
  (O4) U273/TC-A..H/TC-S/actual H_C;
  (O5) explicit C_F/C_K/V/epsilon and 41-division coordinates.
No arbitrary representative is chosen. Therefore the construction produces an actual source-skeleton and a finite-place BPS poly-isomorphism class, but not a complete C.

This is the exact E1 obstruction: E1 would have to show that at least one of O1-O5 is impossible for b=273. No such impossibility is in the frozen source.

## 4. Consequences

- E1 not proved: b=273 conditional counterexample (tasks 256/293/300) remains conditional on a complete C with CFTH/TC/arch; E1 does not close it.
- Complete C not constructed: no actual b=273 C; P6 not refuted.
- P6-true via E1: not established. A P6 proof could still come from b=3 H1-H4, uniform saturation/NPC, or another route, but not from this E1 attempt.
- If E1 were later proved, the b=273 counterexample would be closed; P6 would remain open via b=3/other profiles.

## 5. Proved / conditional / missing

Proved:
- E_546 actual; local I_546/b=273/qhat/e/f; F/K skeleton; mod41 G=H=GL2; Def3.1(a)-(c) skeleton.
- No source bound/contradiction for b=273; no arithmetic/order/mod41 obstruction.
- Task-329 finite-place BPS/Theta class exists up to poly-isomorphism.

Conditional/missing:
- concrete global BPS/Theta-pilot/0-column/target data;
- archimedean theta/BPS and actual H_C/h_inf;
- explicit C equations and TC/CFTH;
- complete C; E1.

## 6. Conclusion

The independent E1 route does not prove impossibility of a b=273 complete C. The E_546 skeleton is admissible at every checkable source-skeleton clause, and the frozen source contains no condition excluding b=273. The finite-place BPS/Theta package exists only up to full poly-isomorphism; the archimedean/zero-label/target/TC/CFTH data are missing, not impossible. E1 remains open; no complete C is constructed; no arbitrary BPS representative is chosen. P6-true via E1 is not established.

Only C9-P6TRUE-E1-COMPLETE-C-20261025.md written. No Lean/Project edits; no mixed/E3; no arbitrary data. target_accepted=false; P6 open; E1 open.
