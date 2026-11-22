# C9 comparator: Lean normalized target vs paper P6_can

Task: task-404 (Comparator: Lean normalized target vs paper P6_can). Owner:
volumedet. Date: 2026-10-25. Short exact comparator/obstruction only. No
normalized surrogate, no black box, no arbitrary data, no mixed/E3, no
Lean/Project edits. Only this file written. `target_accepted=false`.

## 0. Verdict

The existing Lean `PaperP6C6AlignedTarget` is a **finite normalized local**
target, not the paper global canonical P6_can. The exact relation is:

    Lean L:     Q_norm <= h_fin,norm,                          (0.1)
    Paper P_can: Q_can <= d*h_fin,norm + h_inf,                 (0.2)
    P_can/d:    Q_norm <= h_fin,norm + h_inf/d,                (0.3)

with

    Q_norm=Q_can/d,   h_fin,norm=h_bad,can/d,   d=41.          (0.4)

Thus L is not semantically equivalent to P_can. L omits the archimedean
term h_inf (and the exact P_can/d correction h_inf/d); it is equivalent to
the paper comparison only in the degenerate case h_inf=0 (or d=1). There is
no factor-d error in L's qLog/theta pair (both are normalized consistently),
but there is an exact **arch-term gap**.

## 1. What the Lean target actually is

`PaperP6NormalizedValuesActual` defines

    normalizedTheta := thetaLogVolume S / d,
    normalizedValue T := Real.log(c6UnitRefNormalizedData T)/d,
    normalizedValueSet := {normalizedValue T | T in allQPilotRegions},

and

    PaperP6NormalizedTarget :=
      (forall z in normalizedValueSet, z <= normalizedTheta) ∧
      Real.log ||qUnit S|| <= normalizedTheta.                  (1.1)

`PaperP6C6AlignedTarget` adds the identification equalities

    normalizedTheta = C6.normalizedLogVolume(c6Hull),
    Real.log||qUnit|| = C6.normalizedLogVolume(qPilotRegion).   (1.2)

Both sides are C6 finite `ArithmeticTensorTupleBlock` normalized volumes
(factor 1/D, D=d=41). They contain no archimedean place/term. This is
exactly a finite normalized P6, not the source P6_can.

## 2. Exact comparator algebra

Let

    Q_can := -|log q|_packet,   h_can := -|log Θ|_packet  (source),
    Q_norm := Q_can/d,          h_fin := h_bad,can/d      (C6 finite),
    h_inf := arch B_I-zero term.                            (2.1)

C6 h_C = h_fin + h_inf; source h_can = h_bad,can + h_inf = d h_fin + h_inf.
Therefore

    P_can: Q_can <= h_can ⇔ Q_norm <= h_fin + h_inf/d,        (2.2)
    Lean L: Q_norm <= h_fin.                                  (2.3)

Comparator:

    L ⇒ P_can/d if h_inf >= 0  (but not conversely),
    P_can/d ⇒ L if h_inf <= 0  (but not conversely),
    L ⇔ P_can/d  iff h_inf=0 (apart from degenerate boundary equality).
    L ⇔ P_can    iff h_inf=0 (similarly).                      (2.4)

In particular, neither implication is an equivalence in general. The
missing shift is exactly `h_inf/d` on the normalized scale, or `h_inf` on
the canonical scale.

## 3. What a correct comparator would state

To compare Lean normalized quantities to P_can exactly, one must add the
arch term:

    Q_norm <= h_fin + h_inf/d.                                 (3.1)

Equivalently, multiply by d:

    Q_can <= d*h_fin + h_inf = h_can.                          (3.2)

A Lean-ready comparator schema:

```text
theorem paperP6Can_of_leanNorm_plus_arch
  (d : ℕ) (hd : 0 < d)
  (Qcan hcan Qnorm hfin hInf : ℝ)
  (hQ : Qnorm = Qcan/d)
  (hRel : hcan = d*hfin + hInf)
  (hLean : Qnorm <= hfin + hInf/d) :
  Qcan <= hcan

theorem leanNorm_not_paperP6Can_gap
  (d : ℕ) (hd : 0 < d)
  (Qcan hcan Qnorm hfin hInf : ℝ)
  (hQ : Qnorm = Qcan/d)
  (hRel : hcan = d*hfin + hInf)
  (hLean : Qnorm <= hfin)
  (hInf_ne_zero : hInf ≠ 0) :
  -- no general implication either way; the missing term is hInf/d
  Qnorm <= hfin + hInf/d  -- only if hInf>=0
```

`PaperP6C6AlignedTarget` proves the finite hLean C6 identities, but it does
not prove the arch-adjusted (3.1).

## 4. Exact gaps/obstructions

(G1) **Arch term missing.** The Lean target has no `h_inf`; the paper P_can
has `h_inf/d` (normalized) or `h_inf` (canonical). Without an arch value the
comparator cannot be exact. This is not a factor-d issue in qLog/theta; both
are already normalized by d.

(G2) **Global vs finite local.** `PaperP6C6AlignedTarget` is on the finite
C6 tensor block; paper P6_can is global (finite bad + good + arch). The
finite local target is a component, not the global target.

(G3) **q-pilot 82-root.** The Lean qLog is the normalized q log; the source
q-pilot uses qhat (2l=82-root), Q_can=-b/e. No extra82 factor in the
comparator; if one used full q, a factor82 would appear.

(G4) **Arch normalization.** B_I-zero h_inf=log r (F=Q alpha=1); paper
P_can's arch term uses the source packet log with no finite D division.
Replacing it by 0 or by h_inf/d without the source relation is invalid.

(G5) **Target convention.** `PaperP6C6AlignedTarget` is a P6_norm finite
surrogate; it is not the paper P6_can. Calling it P6_can without the arch
term is the exact overclaim.

## 5. Classification

PROVED/EXACT:

- Lean target is normalized finite: Q_norm<=h_fin.
- Source P_can normalized: Q_norm<=h_fin+h_inf/d.
- Exact relation h_can=d h_fin+h_inf; factor d=41; arch shift h_inf/d.
- Equivalence only if h_inf=0 (or d=1); no general implication.
- q-pilot 82-root already in Q_can; no extra82.

CONDITIONAL:

- C6 provenance/finite normalized identification; B_I-zero arch
  h_inf=h_arch,can; target normalization.

IMPOSSIBLE/WITHDRAWN:

- claiming PaperP6C6AlignedTarget is semantically paper P6_can;
- using it as a normalized surrogate for P6_can without adding h_inf/d;
- omitting the arch term or replacing it by 0 arbitrarily.

OPEN/MISSING:

- actual h_inf / arch B_I-zero readout; arch-adjusted comparator;
- paper P6_can global target; P6.

## 6. Conclusion

`PaperP6C6AlignedTarget` is exactly a finite normalized P6 target:
`Q_norm<=h_fin`. Paper P6_can is, after division by d,
`Q_norm<=h_fin+h_inf/d`. The comparator differs by the exact arch term
`h_inf/d`; it is not semantically equivalent unless h_inf=0. The factor d=41
is already consistently applied to both q and finite theta in the Lean
target; the remaining obstruction is the missing arch component/global
assembly, not an additional d factor. No black box, no normalized surrogate
claim, no mixed/E3, no Lean edits.

## 7. Status

Comparator audit only. Only this file written. `target_accepted=false`;
PaperP6C6AlignedTarget=P6_norm finite; paper P6_can requires arch correction;
exact gap h_inf.
