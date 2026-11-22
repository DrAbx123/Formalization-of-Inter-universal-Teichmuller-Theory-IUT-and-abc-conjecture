# C9 smooth target convention/factor audit

Task: task-395 (Independent target convention/factor audit). Owner:
volumedet. Date: 2026-10-25. Natural-language exact statement/obstruction
only. No black box, no arbitrary data, no mixed/E3, no Lean/Project edits.
Only this file written. `target_accepted=false`.

Inputs: IUT III Cor3.12/Prop3.9 packet+procession normalization;
C9-COR312-QPILOT; C9-CANONICAL-NORM-ATTACK (E15); C6
`normalizedLogVolume` (1/D); C9-P6NORM-FACTOR audit; C9-ARCH
B_I-zero normalization.

## 0. Result

The previous task-383 relation `h_C=h_can/d` is **not exact globally**:
the C6 1/D normalization applies to the finite arithmetic-tensor block, while
the archimedean B_I-zero component h_inf is not divided by D=d. The exact
global relation is

    h_C = h_bad_can/d + h_inf,                                  (0.1)
    h_can = h_bad_can + h_inf   (source Θ packet log),           (0.2)
    h_can = d*h_C - (d-1)*h_inf,     d=41.                      (0.3)

Cor3.12 gives `Q_can <= h_can`. Therefore

    Q_can <= d*h_C - (d-1)*h_inf,                               (0.4)
    equivalently Q_can/d + ((d-1)/d)*h_inf <= h_C.              (0.5)

P6_norm `Q_norm<=h_C` is equivalent to `Q_can<=d*h_C`. It follows from
(0.4) **if h_inf>=0**. If h_inf<0, (0.4) does NOT imply P6_norm; the exact
obstruction is the sign/lower bound of the archimedean h_inf.

So:

- **P6_can** (`Q_can<=h_can`) is exactly Cor3.12 and is true (conditional on
  A1-A3/source schema).
- **P6_norm** (`Q_norm=Q_can/d<=h_C`) follows exactly when `h_inf>=0`;
  without h_inf>=0 it is not implied. The exact correct target is (0.5),
  not Q_norm<=h_C.
- **Mixed target** `Q_can<=h_C` is off by both d and arch: source gives
  `Q_can<=d*h_C-(d-1)h_inf`, not `Q_can<=h_C`.
- q-pilot 82-root: already in Q_can=-b/e logp; no 82 factor. Factor d=41
  applies to the finite bad block, not to the arch component.

## 1. Source packet normalization and q-pilot

IUT III Prop3.9(i) packet-normalization: multiplication by e corresponds to
adding 1; procession-normalization averages over j∈F_l^×. Cor3.12's
`-|log q|` and `-|log Θ|` are these packet+procession log-volumes, not the
C6 1/D-normalized arithmetic tensor volumes.

The q-pilot object is the zero locus of q_v; the physical theta values are
q_v^{j²}, with q_v the 2l=82-nd root normalization qhat (q_Tate=qhat^{2l}).
In the C9 tame type qhat=pi^b, so the canonical packet q-pilot log is

    Q_can=-b/e logp   (b=3 or273),                              (1.1)

which is exactly C9's Q value. Using the full q=qhat^{82} would multiply by
82; that is not the source q-pilot normalization. The root rotation is
absorbed by source root units.

## 2. C6 normalization: finite block only

C6 `normalizedLogVolume` = `arithmeticTupleNormalizedLogVolume` divides the
finite tensor-block Haar log by D=finrank_Qp block=d=41. It is a local
finite normalized volume. The global C9 h_C is

    h_C = (finite bad normalized volume) + (good finite 0) + h_inf,   (2.1)

where h_inf is the B_I-zero archimedean readout (h_inf=log r), not a C6
1/D-normalized finite block. Therefore the finite bad part is h_bad_can/d,
but h_inf is undivided:

    h_C=h_bad_can/d+h_inf.                                     (2.2)

Source h_can = h_bad_can + h_arch_can. Under the arch alignment
h_inf=h_arch_can, (0.3) follows. If one incorrectly divides the entire
source h_can by d, one gets task-383's h_C=h_can/d, which misses the arch
term `(1-1/d)h_inf`.

## 3. Exact target algebra

Let a=Q_can, b=h_can, d=41, h=h_C, u=h_inf. Then

    b = d*(h-u)+u = d*h-(d-1)*u,   a<=b.                       (3.1)

Source: `a<=d*h-(d-1)*u`.

P6_norm: `a/d<=h` <=> `a<=d*h`.

From source: `a<=d*h-(d-1)*u`. If `u>=0`, then `d*h-(d-1)u<=d*h`, so
`a<=d*h`; P6_norm follows. If `u<0`, the source RHS is `>d*h`; no
conclusion.

Conversely, the exact inequality (0.5) is

    a/d + ((d-1)/d)u <= h.                                     (3.2)

This is weaker than P6_norm when u<0 (since adding a negative to a/d lowers
the left side) and stronger when u>0. The target must include the arch
correction unless u=0.

P6_can: `a<=b` is exactly source; true.
Mixed: `a<=h` would require `a/d + ... <= h/d`? In any case source gives
`a<=d*h-(d-1)u`, not `a<=h`; off by d and arch.

## 4. Lean-ready statement

Natural-language Lean schema (no Lean edits in this file):

```text
theorem p6_norm_of_cor312
  (d : ℕ) (hd : 0 < d)
  (Qcan hcan hC hInf : ℝ)
  (hRel : hcan = d*hC - (d-1)*hInf)
  (hCor : Qcan <= hcan)
  (hInf_nonneg : 0 <= hInf) :
  Qcan / d <= hC

theorem p6_norm_exact_target
  (d : ℕ) (hd : 0 < d)
  (Qcan hcan hC hInf : ℝ)
  (hRel : hcan = d*hC - (d-1)*hInf)
  (hCor : Qcan <= hcan) :
  Qcan / d + ((d-1 : ℝ)/d) * hInf <= hC

theorem mixed_target_obstruction
  (d : ℕ) (hd : 0 < d)
  (Qcan hcan hC hInf : ℝ)
  (hRel : hcan = d*hC - (d-1)*hInf)
  (hCor : Qcan <= hcan) :
  Qcan <= d*hC - (d-1)*hInf
  -- NOT in general Qcan <= hC or Qcan/d <= hC
```

Proofs: substitute hRel; divide by d>0; hInf_nonneg makes
`d*hC-(d-1)*hInf <= d*hC`, giving P6_norm. The second is rearrangement; the
third is hCor/hRel. Without hInf_nonneg the first fails: for d=2,hC=0,
hInf=-1, hcan=1; taking Qcan=1 gives Qcan/d=1/2>hC=0 while Qcan<=hcan. Thus
`h_inf>=0` is essential (or use the exact target with hInf).
## 5. Exact gap/obstruction

G1. **Arch sign/lower bound.** P6_norm from Cor3.12 requires `h_inf>=0`.
The current corpus has only the upper bound h_inf<=A (and no actual arch
hull); it does not prove h_inf>=0. B_I-zero is a normalization, not a
membership/positivity theorem. Therefore P6_norm is not unconditional.
Alternatively, use the exact target (3.2), which includes h_inf and is true
directly from Cor3.12; but it is not the simple P6_norm Q<=h.

G2. **C6 finite-block vs global arch.** The 1/D factor applies to finite
bad tensor blocks. If the C6 provenance map or global assembly normalizes
arch differently, the exact h_C/h_can relation changes; relation (0.3) uses
the B_I-zero arch alignment h_inf=h_arch_can.

G3. **q-pilot 82-root.** Q_can=-b/e uses qhat; full q would give factor82.
The source q-pilot/q_v identification with qhat is the standard theta-root
normalization; if one instead uses full q, even P6_can acquires 82.

G4. **Target convention.** One must state P6_can, P6_norm, or (3.2). The
mixed `Q_can<=h_C` is not any of them.

## 6. Conclusion

The exact source inequality is P6_can `Q_can<=h_can`. The normalized finite
block relation is `h_can=d h_C-(d-1)h_inf`; hence the exact translated
target is

    Q_can/d + ((d-1)/d) h_inf <= h_C.

P6_norm `Q_can/d<=h_C` follows from this only if h_inf>=0; without an
archimedean lower bound it is not implied. The mixed target `Q_can<=h_C` is
off by d and arch. The q-pilot 82-root normalization is already in
Q_can=-b/e and does not add a factor 82. C6's 1/D normalizes only the
finite bad block; the arch component is undivided. This is the exact
convention/factor statement; the remaining gap is `h_inf>=0` (or use the
arch-corrected target).

## 7. Classification

PROVED/EXACT:

- Prop3.9 packet/procession normalization; Cor3.12 `Q_can<=h_can`.
- Q_can=-b/e (qhat 82-root; no extra82).
- C6 finite 1/D factor d=41; h_can=d h_C-(d-1)h_inf.
- Exact target (3.2); P6_norm requires h_inf>=0; mixed target off by d/arch.

CONDITIONAL:

- C6 provenance/finite normalization; B_I-zero arch alignment
  h_inf=h_arch_can; qhat=q_v source identification.

OPEN/MISSING:

- h_inf>=0 or actual arch lower bound; P6_norm unconditional; target choice.

## 8. Status

Natural-language exact statement/obstruction only. No black box, no arbitrary
data, no mixed/E3, no Lean/Project edits. Only this file written.
`target_accepted=false`; P6_can source; P6_norm conditional on h_inf>=0; exact
arch-corrected target available.
