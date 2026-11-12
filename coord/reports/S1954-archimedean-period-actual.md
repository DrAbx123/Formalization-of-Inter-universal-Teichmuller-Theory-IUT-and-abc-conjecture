# S1954: the period-carrying (full paper) archimedean log-shell — constructed, with the exact normalization boundary

Date: 2026-11-01.  Task: extend/construct the **full paper**
`ArchimedeanLogShellDatum` (with the `2πi` period generator, the fundamental
segment endpoint difference and the log-link upper semi-commutativity) and prove
the actual archimedean unit ball / `π`-disk satisfies it — or give the exact
first missing.  No fake period.

## Result (short)

**The full datum is constructed at every complex archimedean place, with the
actual `π`-disk as log-shell and the actual `2πi` as period; and the reduced
S1950 normalization can provably never satisfy it.**  EXIT=0, zero errors, zero
warnings, no `sorryAx`; `#print axioms` on all probed declarations =
`[propext, Classical.choice, Quot.sound]`.

The exact first missing is **not** a proof obligation about the closed unit
ball: it is the normalization.  The paper's archimedean log-shell is
`I_k = {a | |a| ≤ π}`, which *contains* the closed unit ball `O_k` and is
*not* contained in it; S1927's reduced `ArchimedeanLogShellDatum` requires
`logShell ⊆ O_k`.  At a complex place those two conditions are **incompatible**
(`no_logShell_subset_unitBall`), because the period is a difference of two
points of the log-shell, forcing `‖period‖ ≤ 2 = diam O_k`, while the actual
period has `‖period‖ = 2π > 2`.

## Source (checked against the local corpus)

* [IUTchIII], **Remark 1.2.2, (ii)** (concrete model, `v ∈ V^arc`,
  `k = K_v` complex archimedean):
  `O_k = {|a| ≤ 1}`, `O_k^× = {|a| = 1}`, `exp_k : k → k^×`, and
  `I_k = {a ∈ k | |a| ≤ π}`, with (b^arc) `O_k^◃ ⊆ O_k ⊆ I_k` and
  (c^arc) `O_k^× ⊆ exp_k(I_k)`.
* [IUTchIII], **Definition 1.1, (ii)**: the log-shell is the
  `Ψ^×_{log(†F_v)}`-orbit of the closed line segment preserved by `±1` whose
  endpoints differ by a generator of the kernel of `Ψ∼ ↠ Ψgp`.  In the concrete
  model this is `[-πi, πi]` (endpoint difference `2πi`, the generator of
  `ker exp_k = 2πi Z`), whose `O_k^×`-orbit is exactly the `π`-disk.
* [IUTchIII], **Remark 1.2.2, (iii), (iv)**: "upper semi-commutativity" at
  `v ∈ V^arc` is a *surjectivity/containment*, not an equality, and no "lower
  semi-commutativity" is available.
* [IUTchIII], **Remark 3.9.4, (vi)**: `O_k^× ⊆ k` has length `2π` (the norm of
  the period `2πi`).
* [IUTchI], **Definition 3.1, (a)**: `F` is a number field with `√-1 ∈ F`;
  hence all archimedean places of an initial Θ-datum are complex — which is why
  [IUTchIII], Remark 1.2.2, (ii) can say "Thus, `K_v` is a complex
  archimedean field".

## What is constructed (Lean, kernel-closed)

File: `tmp/sheaf/xif/paper/S1954ArchimedeanPeriodActual.lean` (811 lines).

Structure (the full paper datum):

    structure PaperArchimedeanLogShellDatum (D) (w) where
      [moduleK : Module Real w.Completion]
      logShell : Set w.Completion
      isCompact_logShell / convex_logShell / zero_mem_logShell      -- (a^arc)
      unitBall_subset_logShell                                       -- (b^arc)  O_k ⊆ I_k
      period : w.Completion
      period_ne_zero
      exp_period : archimedeanExp D w period = 1
      period_generates_kernel : ∀ z, archimedeanExp D w z = 1 ↔ ∃ n : ℤ, z = n • period
      fundamentalSegment : Set w.Completion
      fundamentalSegment_isSegment : ∃ a b, fundamentalSegment = segment Real a b
                                        ∧ b - a = period ∧ b = -a
      fundamentalSegment_endpoints_mem : ∃ a b, a ∈ fundamentalSegment ∧ b ∈ fundamentalSegment
                                        ∧ b - a = period ∧ b = -a
      fundamentalSegment_subset_logShell
      logShell_eq_unitOrbit : ∀ x, x ∈ logShell ↔ ∃ u s, ‖u‖ = 1 ∧ s ∈ fundamentalSegment ∧ x = u * s
      units_subset_exp_logShell : archimedeanUnitSphere D w ⊆ archimedeanExp D w '' logShell   -- (c^arc)

Note the deliberate *reversal* of the reduced containment: the full datum has
`O_k ⊆ logShell` (b^arc), not `logShell ⊆ O_k`.

The three features S1950 listed as missing are exactly:

* `archimedeanExp` = the actual exponential of the archimedean local field
  (`Complex.exp` transported at a complex place, `Real.exp` at a real place);
  `paperPeriod = 2πi` with `archimedeanExp_paperPeriod`,
  `paperPeriod_ne_zero`, `norm_paperPeriod : ‖2πi‖ = 2π`, and the exact kernel
  `archimedeanExp_eq_one_iff : exp z = 1 ↔ ∃ n, z = n • period`;
* `paperFundamentalSegment = [-πi, πi]` (image of the `C`-segment under the
  canonical iso), with `paperFundamentalSegment_endpoint_sub` (endpoint
  difference = the period), `neg_mem_paperFundamentalSegment` (preserved by
  ±1), `paperFundamentalSegment_norm_le`, and the parametrisation
  `mem_paperFundamentalSegment_iff : x ∈ seg ↔ ∃ r ∈ [-π, π], x = e.symm (r • i)`;
* the orbit identity `mem_paperLogShell_iff_unit_mul_segment` (the paper's
  "orbit of the segment under the local units"), plus
  `smul_unit_mem_paperLogShell` (invariance under `O_k^×`);
* the log-link upper semi-commutativity:
  `archimedeanUnitSphere_subset_exp_paperLogShell` (c^arc), its packaged form
  `PaperArchimedeanLogShellDatum.logLink_upperSemi`, and the failure of the
  reverse containment `not_exp_paperLogShell_subset`
  (`exp_k(I_k) ⊄ I_k`, since `exp(π) = e^π > π`), i.e. genuinely upper semi.

The construction `paperArchimedeanLogShellDatum D w hw` (`hw : w.IsComplex`)
has `logShell = {x | ‖x‖ ≤ π}` (definally, `@[simp]`), `period = 2πi`, and the
fundamental segment `[-πi, πi]`.  Convexity/compactness are the actual metric
facts transported along the isometric field isomorphism; nothing is fitted.

## Exact boundary (the "first missing")

1. `no_logShell_subset_unitBall`: for **every** full datum at a complex place,
   `¬ F.logShell ⊆ archimedeanUnitBall D w`.  Proof: the period is a difference
   of two log-shell points, so `‖period‖ ≤ 2`; but
   `two_pi_le_norm_period` derives `2π ≤ ‖period‖` from
   `period_generates_kernel` (the period lies in `2πi Z ∖ {0}`).
2. `s1950_not_full`: S1950's datum (whose log-shell is the whole actual closed
   unit ball) is not the log-shell of any full datum.
3. `real_place_not_inhabited`: at a real place the full datum is
   **provably empty** — the period group of `exp_R` is trivial, so
   `exp period = 1` forces `period = 0`, contradicting `period_ne_zero`.
   This is consistent with [IUTchI], Def. 3.1, (a) (`√-1 ∈ F`) and
   [IUTchIII], Rem. 1.2.2, (ii); it means the "full" upgrade of S1927's
   `S1927FirstMissing` must be quantified over complex places.
4. `archimedeanUnitBall_ssubset_paperLogShell`: `O_k ⊊ I_k` (strictly, by
   `π ∈ I_k ∖ O_k`), so the `π`-disk is a genuine enlargement, not a relabel.
5. `s1954_exact_boundary`: the conjunction of (1)–(3) as one theorem.

Thus the passage from S1950's plain-completion-norm unit ball to the paper's
`π`-normalized log-shell is forced by the period generator `2πi`; it is a
change of normalization, not an unproved lemma.

## Evidence

* source: `tmp/sheaf/xif/paper/S1954ArchimedeanPeriodActual.lean`, 39461 bytes,
  811 lines, SHA256
  `E7BF32A4DB8ECEB8B1E4AFE8C076C5BB7C8BC36B808BA7CF92562E67F170ECC5`;
* build: `lake env lean -j1 -R D:\\lean -o <olean> <file>`, **EXIT=0**, no
  errors, no warnings, no `sorry`/`admit`/`axiom` (grep clean except the
  docstring text);
* olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1954ArchimedeanPeriodActual.olean`,
  1129600 bytes, SHA256
  `55D320A240C99D4D0A1A9C6EC38CD947C408DCC971B01AC3A55CD7CFDD156F29`;
* consumer `tmp/sheaf/xif/paper/_S1954Consumer.lean` (EXIT=0; olean
  SHA256 `E40132A726C91B8E74472AF8CF095916A0411155B5C4986076F387BD3AE03F7D`):
  `#check` on the structure, the construction, the three period features and
  the boundary theorems, plus four `example`s using them;
* `#print axioms` on `paperArchimedeanLogShellDatum`,
  `archimedeanExp_eq_one_iff`,
  `archimedeanUnitSphere_subset_exp_paperLogShell`,
  `mem_paperLogShell_iff_unit_mul_segment`, `two_pi_le_norm_period`,
  `no_logShell_subset_unitBall`, `real_place_not_inhabited`,
  `s1950_not_full`, `s1954_exact_boundary`: all
  `[propext, Classical.choice, Quot.sound]`.

Status flags (per SHEAF): `statement_compiles = true`,
`proof_body_checked = true` (full kernel check of this file),
`kernel_closed = true` for the listed declarations, `target_accepted` — not
claimed (no comparator run in this package).

## Exact open items (honest)

* The full datum is not inhabited at real archimedean places (proved
  impossible, not a gap).  If a consumer needs `S1927FirstMissing` over *all*
  infinite places with the full period structure, that type is empty; the
  paper-faithful statement is over complex places.
* The Kummer evaluation square (`S1927KummerEvaluationSquareActual`) remains
  the other named missing input of `S1927FullLogKummerUQ` (unchanged here).
* No comparison with the abstract `Ψ∼`/`Ψgp` Frobenioid-theoretic model above
  the concrete `k`-level of Remark 1.2.2, (ii), is made; the file works at the
  concrete complex-archimedean-field level, exactly as the paper's remark does.
* The four coric vertices env/gau/LGP/lgp and the theta-link are untouched.

## Consumer

The direct consumer is the S1927/S1950 archimedean gap: `s1950_not_full` and
`s1954_exact_boundary` state that the reduced unit-ball datum cannot be extended,
and `paperArchimedeanLogShellDatum` supplies the period-carrying replacement.  A
subsequent package can replace S1927's `S1927FirstMissing` by the complex-place
version `(w) (hw : w.IsComplex) → PaperArchimedeanLogShellDatum D w` (inhabited
here) and record the real-place emptiness as a hypothesis boundary.

## Suggested next step

Wire `paperArchimedeanLogShellDatum` into `S1927FullLogKummerUQ` as the
archimedean component over complex places only (a definitional variant
`S1927FirstMissingComplex`), so the remaining exact missing of the full
log-Kummer package is *only* the Kummer evaluation square.
