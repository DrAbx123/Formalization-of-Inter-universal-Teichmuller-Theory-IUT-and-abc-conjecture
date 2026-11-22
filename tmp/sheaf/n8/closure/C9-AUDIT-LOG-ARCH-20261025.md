# C9 audit: log-domain and archimedean independence

Task: task-161 (C9 audit: log-domain and archimedean independence).
Owner: volumedet. Date: 2026-10-25. Stage1 natural-language audit only.
No Lean/Project/target edits. Only this file written. `target_accepted=false`.

Audited files:

- `C9-LOG-DOMAIN-EXTEND-20261025.md` (task-146), 200 lines, SHA256
  `cc52a8cf0d5fb56172a7af2f6fb0c5c57eb726a5a459d3ccde42fddd3daf2dfa`;
- `C9-ARCHIMEDEAN-20261025.md` (task-150), 251 lines, SHA256
  `f4c7afe112c238d7f5547461c1500ac45a73e49075bddf366fe8b1e5a53e9957`.

Corrections read: `C9-SYMPLECTIC-SOURCE-20261025.md` (task-147),
`C9-IND1-GLOBAL-20261025.md` (task-149), and `C9-MODP-CERTIFICATE-20261025.md`
as corrected in task-155. The audit checks formulas, signs, branch labels and
the conditional/donor-dependent status; it does not add a new attack.

## 0. Executive verdict

| file | valid/donor-independent | donor-dependent/conditional | error/overclaim |
|---|---|---|---|
| task-146 log-domain | p-adic exp threshold n0; e=p-1 boundary; exp/log inverse on U^{n0}; O_K lattice; exp(pz) | Teichmuller branch (a)/(b); source restriction D_K; Aut(G_K) shell preservation; wild-ramification trace/symplectic formulas | log series claimed to diverge/only converge on U^{n0}; J_K=log(O_K^×)=m^{n0} as full log image; volume formula drops f for f>1 |
| task-150 archimedean | IV container bound (j+1)log pi; procession average (l+5)/4; dimension factor zero; sign warning; arch-only insufficiency direction | finite b=3,b=273 values inherit inferred donor/basis/orbit generation; p_{vQ}=e normalization; larger-b monotonicity | §4 uses TAME (10) with -c j but quotes h from aligned (15); b=273 value -38736/41 is B=I branch, not A=O_K; downstream tasks 156/162 used base 41 instead of p=12301 for radius |

No global conclusion changes: both files remain stage1 conditional research;
task-150's main archimedean-only insufficiency conclusion survives the
corrections below, with corrected labels/numbers.

## 1. Audit of task-146 (log domain)

### 1.1 Valid, donor-independent

1. The p-adic exp threshold is correctly stated. For x in m^n,
   v_p(x^k/k!) >= k n/e - v_p(k!), and Legendre's estimate
   v_p(k!) <= (k-1)/(p-1) gives uniform convergence once n/e >= 1/(p-1),
   i.e. n >= e/(p-1). Thus

       n0 = ceil(e/(p-1))

   is a valid sufficient/necessary threshold for exp on m^n (uniform
   convergence; necessity follows from k=p^t terms as in the file).
2. For e=p-1, n0=1 and exp converges on m; the extension of the tame
   log/exp inverse statement to e<=p-1 is valid.
3. On the restricted domain U^{n0}=1+m^{n0}, log and exp are inverse; the
   displayed estimates and the Teichmuller decomposition
   O_K^× = mu_{q_res-1}(K) x U^1 are standard and valid. The (a)/(b)
   Teichmuller convention is correctly separated from the analytic series.
4. If J_K is defined as log(D_K) with D_K=mu·U^{n0}, then
   J_K=m^{n0}, I_K=p^{-1}J_K=m^{n0-e}, and the integer-lattice statement
   L_K=O_K+m^{n0}=O_K (n0>=1) are correct algebra.
5. exp(pz) for z in O_K is safe for every e: n0<=e, so
   v_p(pz)>=1>=n0/e, and log(exp(pz))=pz. This part is donor-independent.

### 1.2 Errors / overclaims

**Error 1 (log convergence).** The file asserts that for n<e/(p-1), taking
k=p^t makes the log-term valuation go to -infinity. For log on x in m^n the
term x^k/k has valuation

    k n/e - v_p(k) = p^t n/e - t  ->  +infinity,

not -infinity. The p-adic log series therefore converges on all U^1=1+m
(indeed for all x in m); the n0 threshold is the convergence threshold for
**exp**, not for log. The statement 'U^1/U^{n0} has no p-adic log' is false
for the power-series log.

**Error 2 (J_K as full log image).** From the restricted-domain convention
D_K=mu·U^{n0} the file derives J_K=m^{n0}, and then writes
`J_K=log(D_K)`. That is correct only for the artificially restricted D_K.
For the full p-adic log on U^1 (or on O_K^× with Teichmuller zeros), the image
contains the linear term x, hence is not confined to m^{n0}; in particular
`log(O_K^×)=m^{n0}` for e>p-1 is not a theorem of convergence. This is the
main conditional/overclaim: J_K=m^{n0} depends on a source convention
restricting log to U^{n0}, not on the analytic log domain.

**Minor error 3 (volume factor).** The formula
`logvol_O(m^n)=n f/e · log p = (n/e)·log p` drops f in the second equality;
for f>1 only `n f/e` is correct. The tame bad profile uses f=1 (totally
ramified), so the numerical tame applications are unaffected; the general
statement is wrong as written.

### 1.3 Donor-dependent/conditional

- Teichmuller root log=0 and D_K=mu·U^{n0} are source conventions; the file
  itself marks this. The audit confirms they are not consequences of the
  analytic power series.
- The sentence that Aut(G_K)'s additive image preserves m^{n0} and the
  normalized shell is inferred from the corrected symplectic donor and the
  basis alignment; it is not a paper theorem. Under task-147 it must carry
  TC-S and the inferred-basis caveat.
- The wild-ramification warning in §5.3 is correct: tame trace/W=ker Tr and
  floor(bj^2/e) formulas cannot be copied to e>p-1. The file does not prove
  the wild analogue; this is an acknowledged gap, not an error.

### 1.4 Verdict for task-146

Valid core: exp threshold n0, e=p-1 boundary, restricted exp/log inverse,
integer lattice conditional on J_K=m^{n0}, exp(pz), Teichmuller branch
separation. Error: log-domain/divergence statement and full-log J_K claim;
minor f factor. The file's own §2(b) and §8 mark the source-convention
dependence, but §1/§2/§7 still use the stronger 'log domain = U^{n0}'
language and should be corrected.

## 2. Audit of task-150 (archimedean)

### 2.1 Valid, donor-independent

1. IV Prop1.5(iii)(iv)/Thm1.10(vii): the archimedean tensor container is
   pi^{j+1}B_I, and under the normalization logvol(B_I)=0 its log-volume is
   (j+1) log pi. The direct-sum/tensor dimension factor 2^{|I|-1}|V|^{|I|}
   contributes zero normalized log-volume; only the radial factor remains.
2. The procession average is correct: with m=(l-1)/2,

       (1/m) sum_{j=1}^m (j+1) = (m+3)/2 = (l+5)/4.

   For l=41 this is 46/4=11.5, so A_arc <= 11.5 log pi = 13.1643937...
   natural-log units.
3. The bound is an upper bound, not a lower bound; the file correctly states
   that IV gives only the container upper bound and no actual archimedean
   lower bound. This is an important valid limitation.
4. Constants: 11.5 log(pi)/log(43)=3.5000514..., and for p=12301
   11.5 log(pi)/log(12301)=1.3978745..., both match the file.
5. Sign warning: the paper's radial archimedean log-volume is positive
   ((j+1)log pi), while the Lean readout is
   `absLogAddHom K u = -Real.log ||u||` and `archimedeanDelta r = -Real.log r`.
   Thus direct comparison needs a minus sign (or use -archimedeanDelta).
   The audit checked the Lean declarations and confirms this sign warning is
   valid and important.
6. The archimedean-only insufficiency direction: for the uniform A=O_K branch
   and l=41, b=3 deficit 408/41=9.9512 > 3.5001 (p>=43) and >1.3979
   (p=12301); b=273 deficit > 938. The archimedean container cannot cover
   these A-branch deficits. This conclusion is stable.

### 2.2 Errors / overclaims / mislabeled data

**Error 4 (formula (10) vs numerical h).** In §4 the file writes TAME (10)
with the term `-c j`, c=(e-1)/(2e)=20/41. At rho=1 and e=41,

    ell_j^Sp(10) = -(20/41) j - s_j - 41^{-(j+1)},
    h_10 = (1/20) sum ell_j^Sp
         = -210/41 - 10 - (1/20) sum_{j=1}^{20} 41^{-(j+1)}
         ≈ -15.122  (not -411/41 ≈ -10.024).

The quoted `h=-411/41` is the aligned (15) quantity
`h_A=-(1/20)sum(s_j+1/41)`, which omits the `-c j` tensor-order loss. The
file's formula and numbers therefore refer to different bounds. The arch
comparison conclusion still holds for the aligned `h_A`, but the label
'TAME (10)' must be replaced by '(15)-aligned, without -c j'.

**Error 5 (b=273 branch label).** The table's b=273 value `-38736/41` is the
conditional B=I branch of TAME §7, not the A=O_K branch. The corrected
C9-UNIFORM values are

    A=O_K: -39156/41,  Q-B deficit 38883/41;
    B=I:   -38736/41,  Q-B deficit 38463/41.

The file labels the row as generic `h_p`; it must say B=I (conditional and
unproved). Using A would make the deficit larger, so the arch-only
insufficiency conclusion is unchanged; only the number/branch label is wrong.

**Conditional monotonicity.** The sentence 'larger b only increases deficit'
is not a paper theorem and is not derived from the corrected donor in this
file; it is an affine-period inference from TAME. Keep it conditional.

### 2.3 Donor-dependent/conditional

- §4 finite numbers inherit the TAME §7 inferred symplectic donor, inferred
  trace/symplectic basis alignment, orbit generation and local naturality.
  The file's §0.1 already flags this; the audit confirms the flag is
  necessary and applies to the b=3/b=273 numbers.
- `p_{vQ}=e` and the exact archimedean normalization are quoted from
  III/IV Rmk3.1.1; this audit did not independently re-read those paper loci.
  Treat the normalization constant as paper-interface conditional, not
  independently verified donor-independent.
- The direction analysis in §5/§6 (exp vs p-adic log, Kummer roots/powers,
  Ind1/Ind2/Ind3, q-pilot finite source) is donor-independent at the
  natural-language level and is consistent with the correction notices.


## 2.4 Downstream radius-base check (tasks 156/162; requested by lead)

This audit was asked to verify the archimedean radius base used downstream.
The criterion is

    C7:  r_inf >= pi * p^{d_p},

where `d_p=D_C^Sp/log p` is the finite residual in log-p units.  The base
must be the bad prime p=12301, not the ramification index e=41.

Old task-156 formulas A18/A19 used `pi*exp(D_C^Sp)` and omitted the log-p
factor; old task-162 formulas D1/D2 used `41^{d_p}` and hence the wrong base.
Both are false as displayed.

Correct values for e=41, p=12301, rho=1, B=O_K branch:

- b=3, d_p=408/41:

      r_inf >= pi * 12301^{408/41}
            ~= 1.5741451258619702e41,
      log10 r_inf ~= 41.197044769,
      d_p log10 p ~= 40.699894896.

- b=273, d_p=38883/41:

      r_inf >= pi * 12301^{38883/41},
      d_p log10 p ~= 3878.759836402,
      log10 r_inf = log10(pi) + 3878.759836402 ~= 3879.256986275.

Thus the lead's `~1.57e41` and `~3878.76` are the correct orders: the
`3878.76` is `d_p log10 p`; the full radius including the shell factor pi has
log10 ~3879.257.  The old values ~3.5e16 (b=3) and ~1530 (b=273) are wrong
by the base-41/exp omission.

Independent check: `408/41 log10(12301)=40.6999`, plus `log10(pi)=0.4971`
gives 41.1970; `38883/41 log10(12301)=3878.7598`, plus 0.4971 gives
3879.2570.  The decimal orders are not a proof of the residual formula; they
only check the radius conversion C7.

## 2.5 Verdict for task-150

Valid: archimedean upper bound (j+1)log pi and procession average
(l+5)/4 log pi; dimension factor zero; sign correction; upper-bound-only
limitation; arch-only insufficiency for the A branch. Error: formula (10)
is conflated with (15)-aligned values; b=273 row is B=I not A. Conditional:
all finite values and larger-b monotonicity depend on inferred donor/basis
assembly and should not be cited as paper-level theorems.

## 3. Cross-file consistency after correction 2

- Neither file claims a target-containment `F(Hull(...)) subset H_C`;
  task-150's arch bound is a container upper bound and remains valid as such.
- task-146's `J_K=m^{n0}` is a restricted-domain convention, not a target
  proof; task-150's note that finite values are donor-dependent is correct.
- The corrected C9-IND1 conditions TC-A..TC-H and TC-S remain missing for
  any use of these bounds in the actual target container. No update of
  `C9-UNIFORM-HULL` or `C9-MODP-CERTIFICATE` is needed here; both already
  carry correction 2.

## 4. Exact arithmetic checklist

| quantity | value | check |
|---|---|---|
| n0 at e=41,p=12301 | 1 | e/(p-1)=41/12300<1, ceil=1 |
| (l+5)/4, l=41 | 46/4=11.5 | sum_{j=1}^{20}(j+1)/20 |
| 11.5 log pi | 13.1643937 | natural log |
| 11.5 log pi/log43 | 3.5000514 | p>=43 |
| 11.5 log pi/log12301 | 1.3978745 | p=12301 |
| b=3 aligned h_A | -411/41=-10.02439 | (15)-aligned |
| b=3 formula (10) h_10 | -210/41-10-tiny ~ -15.122 | includes -c j |
| b=273 aligned A | -39156/41=-955.024390 | A=O_K |
| b=273 B=I | -38736/41=-944.780 | conditional B |

Correction: the aligned A value for b=273 is -39156/41, numerically
-955.024390; the B=I value is -38736/41, numerically -944.780488. The table
in task-150 used the B value with a generic label.

## 5. Final classification summary

### task-146
- VALID/donor-independent: exp threshold n0=ceil(e/(p-1)); e=p-1 boundary;
  restricted exp/log inverse on U^{n0}; exp(pz); Teichmuller decomposition;
  integer lattice given J=m^{n0}.
- CONDITIONAL: source restriction D_K=mu U^{n0}; Teichmuller roots log=0;
  J_K=m^{n0}; shell I_K; volume (2.3) with f tracked; wild-ramification
  analogue; Aut(G_K) shell preservation (TC-S/basis alignment).
- ERROR/OVERCLAIM: log divergence/domain claim; full-log J_K=m^{n0};
  dropped f in volume formula.

### task-150
- VALID/donor-independent: IV arch container bound; procession average;
  dimension factor zero; sign correction; upper-bound-only; A-branch
  arch-only insufficiency direction and constants.
- CONDITIONAL/DONOR-DEPENDENT: b=3/b=273 finite values; larger-b monotonicity;
  p_{vQ}=e normalization; any target-container use (TC-A..TC-H, TC-S).
- ERROR/MISLABEL: formula (10) vs (15)-aligned h; b=273 row is B=I not A.

Neither file proves the original C9/P6 target. No global h_C<Q_C or
h_C>=Q_C conclusion is accepted here.

## 6. File hashes (audited versions)

- task-146: `C9-LOG-DOMAIN-EXTEND-20261025.md`, 200 lines; SHA256
  `cc52a8cf0d5fb56172a7af2f6fb0c5c57eb726a5a459d3ccde42fddd3daf2dfa`.
- task-150: `C9-ARCHIMEDEAN-20261025.md`, 251 lines; SHA256
  `f4c7afe112c238d7f5547461c1500ac45a73e49075bddf366fe8b1e5a53e9957`.
- downstream radius check: task-156 `C9-ARCH-GLOBAL-20261025.md` and task-162
  `C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md`; their base-41/exp radius lines
  must be replaced by C7 `pi*p^{d_p}` as in §2.5.

The hashes are also repeated in the task-board final report and delivery
message.

## 7. Acceptance record

Stage1 natural-language only. Lean/Project/kernel/comparator/independent
review not run. Only this audit file written. `target_accepted=false`;
no target change; no new attack.
