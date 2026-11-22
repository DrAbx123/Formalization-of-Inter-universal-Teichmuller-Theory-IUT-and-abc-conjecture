# C9 review: scope/unconditionality of the Cor3.12 NL proof

Task: task-422 (Review scope/unconditionality of Cor3.12 proof). Owner:
volumedet. Date: 2026-10-25. Review only; no rewrite. No Lean/Project edits,
no mixed/E3. Only this file written. `target_accepted=false`.

Reviewed file: `C9-COR312-UNCONDITIONAL-NL-20261025.md` (196 lines).

## 0. Verdict

**ACCEPT for scope and unconditionality.** The proof stays in the paper
packet+procession-normalized Cor3.12 scope and quantifies over admissible
initial Theta-data without adding a C9 target, normalized surrogate, factor
d/82, arch h_inf, numerical epsilon, mixed profile, or extra hypothesis.

The proof is a source-level paraphrase/deduction from Theorem3.11,
Proposition3.9, Remark3.9.5 and the log-theta-lattice, not an independent
formalization of those source theorems. That is a dependency, not an extra
hypothesis; it does not violate this scope review.

## 1. Quantifier and theorem statement

The reviewed statement:

    for every collection C of initial Theta-data as in IUT I Def3.1,
    -|log Theta| in R,  -|log Theta| >= -|log q|,
    C_Theta >= -1 for every real C_Theta with
    -|log Theta| <= C_Theta*|log q|.

This matches IUT III Cor3.12/Theorem B. The source hypothesis is 'in the
situation of Theorem3.11', i.e. the given admissible initial Theta-data; the
proof does not add a complete-C construction, B branch, profile, good-place,
TC, or arch assumption. Quantifier ACCEPT.

## 2. Step-by-step review

### Step 1 (setup, Def3.8, q/Theta pilots) — ACCEPT

Defines q-pilot via q_v up to torsion, Theta-pilot via theta values q_v^{j²},
and the Theta×mu LGP-link as a full poly-isomorphism of F^⊩▶×mu-prime-strips.
These are the source definitions; no C9 normalized object enters.

### Step 2 (Theorem3.11 multiradial algorithm, IPL/SHE/APT) — ACCEPT

Uses Theorem3.11/Remark3.11.1 as source. No extra hypothesis on C; the
indeterminacies Ind1/Ind2/Ind3 are the source ones. The F^value/F^unit split
is source-level; no factor d/82 inserted.

### Step 3 (holomorphic hull, Remark3.9.5 Ob1-Ob3) — ACCEPT (source-level)

The hull and determinant/log-volume comparison are the source Ob1-Ob3/
Prop3.9 constructions. The proof does not construct an explicit complete C
and does not substitute a C6 finite-block normalized volume. Finiteness uses
the source compactness of 1,°U_{j,vQ}; no numerical epsilon.

### Step 4 (fixed q-pilot/SHE, xi-e) — ACCEPT

Uses the fixed q-pilot value -|log q| and SHE exactly as xi-e; q-pilot is not
subject to Ind1/2/3, while possible outputs are. No normalized or arch term
is substituted.

### Step 5 (closed loop/formal quotient, xi-f) — ACCEPT (source-level)

The sQ1-sQ4/cQ3/cQ4 chain and Ob9-1 formal indeterminacy are supported by
Remark3.9.5(viii)-(ix) and Ob9. In particular Ob9 indeed states that passing
to realified semi-simplifications induces a natural bijection between
log-volumes of hulls in the domain and codomain of the log-link; Ob9-1 treats
tensor-power-twist/nabla/log-link-iterate indeterminacies as compatibility
conditions for coarse invariants. The proof's 'approximation' is this
indeterminacy quotient, not an extra numerical epsilon. ACCEPT as the source
xi-f deduction.

### Step 6 (inclusion and inequality) — ACCEPT

From -|log q| in R_{<= -|log Theta|} obtains -|log q|<=-|log Theta| and
C_Theta>=-1. This is formal algebra, exactly the source conclusion; signs
are consistent with the source's negative notation.

### Step 7 (unconditionality) — ACCEPT

The proof uses only admissible initial Theta-data, Theorem3.11,
Remark3.11.1, Proposition3.9, Remark3.9.5, and the LGP/log-link structures.
It does not use:

- a C9 normalized target;
- a factor d=41 or an extra 82;
- a separate arch h_inf;
- a numerical epsilon;
- mixed profile/row max/b=273 no-go;
- a B=O_K/B=I branch;
- a complete C construction.

Thus 'unconditional' means over admissible initial Theta-data, with the
source theorems as dependencies. ACCEPT.

## 3. Dependencies vs extra hypotheses

The proof is unconditional **relative to** the source theorem package
(Theorem3.11, Proposition3.9, Remark3.9.5, log-theta-lattice). Those are
cited source results, not additional hypotheses on C. A reader who wants a
first-principles proof must expand those source theorems; that is a
completeness/source-expansion issue, not a scope/unconditionality violation.

The reviewed proof does not reproduce every source line, but it does not
insert any definition, normalization, or estimate outside the source scope.

## 4. No prohibited substitutions found

| item | present? | note |
|---|---|---|
| C9 normalized target | NO | packet+procession source volumes only |
| factor d=41 | NO | no finite-block 1/D |
| extra 82 | NO | q-pilot q_v/Theta values are source |
| arch h_inf | NO | source full log includes arch, no C9 h_inf |
| numerical epsilon | NO | indeterminacy quotient, not epsilon |
| extra hypothesis | NO | only admissibility/Thm3.11 situation |
| mixed/E3 | NO | uniform source initial data only |
| b=273 no-go | NO | universal b-independent proof |

## 5. Final accept/reject

**ACCEPT** the proof for its stated scope and unconditionality over admissible
initial Theta-data. It correctly proves the source-level Cor3.12 schema
without C9 normalized/arch/factor substitutions.

CAVEAT: acceptance is at the source-proof/paraphrase level. It is not an
independent expansion of Theorem3.11/Prop3.9/Remark3.9.5, and it does not
replace a full source verification. This caveat does not change the scope
verdict.

## 6. Classification

ACCEPTED:

- Paper P6_can quantifier and source packet+procession normalization;
- Step1-Step7 as source-level deduction;
- no factor d/82, arch h_inf, epsilon, mixed/E3, extra hypothesis.

NOT CLAIMED:

- independent formal proof of Theorem3.11/Prop3.9/Remark3.9.5;
- expansion of every Ob/sQ/cQ source line.

## 7. Status

Review only; no rewrite. No Lean/Project edits, no mixed/E3. Only this file
written. `target_accepted=false`; scope/unconditionality ACCEPTED; source
proof-level accepted with dependency caveat.
