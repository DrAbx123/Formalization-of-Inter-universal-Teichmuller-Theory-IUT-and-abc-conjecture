# S1975 — joint continuity of `G_v` on the ind-topological `Ψ~`: exact first missing

Consumer: S1962 R1 package (`R1JointContinuousActionMissing`, S1962R1AbstractActionActual.lean).
Package file: `tmp/sheaf/xif/paper/S1975JointContinuityActual.lean` (EXIT = 0, no `sorry`, no `axiom`).

## Result

**The limit joint-continuity statement is NOT proved — and is not refuted — here.**  Instead the
exact analytic input is isolated, the whole transport chain to the S1962 statement is machine-checked,
and the missing input is identified with a strict topology-inclusion statement.

Proved (unconditional, axioms `[propext, Classical.choice, Quot.sound]` only):

| name | content |
|---|---|
| `norm_galois_smul` | every actual `G_v`-automorphism of `Θ = SourceAlgebraicClosure (QPlace v)` is an isometry of the spectral norm |
| `isOpen_ind_ball` | absolute-value balls `{y ‖ ‖y - z‖ < ε}` are open for the ind topology |
| `ind_le_norm` | every norm-open set is ind-open — the *only* inclusion the tree's final-topology definition supplies |
| `IndCarrierBallNeighborhood` (def) | the exact first missing: every ind-open set `∋ z` contains a norm ball around `z` |
| `indCarrierBallNeighborhood_iff` | that property ⟺ `sourceAlgebraicFieldIndTopology = inferInstance` (ind topology = norm topology) |
| `jointContinuousGaloisEvaluation_of_ballNeighborhood` | missing input ⟹ the evaluation map `G_v × Θ → Θ` is jointly continuous for the ind topology |
| `jointContinuous_psiTilde` | same, transported to `Ψ~` through `sourceUnitPerfectionIndHomeomorph` |
| `r1JointContinuous_of_ballNeighborhood` | **`∀ v, IndCarrierBallNeighborhood (QPlace v) → R1JointContinuousActionMissing v`** |

The reduction is the genuine continuity-with-parameters argument (no fake continuity): at
`(σ₀, y₀)` use the open coset `σ₀ · Gal(Θ/E)` of the open stabiliser of `y₀`
(`stabilizer_isOpen_of_isIntegral`, `Mathlib/FieldTheory/KrullTopology.lean`) and the ind-open ball
around `y₀`; on that product `σ y - σ₀ y₀ = σ (y - y₀)`, so the isometry `norm_galois_smul`
carries the smallness over.

## Why this is the *exact* first missing, and why it is not a formality

`isOpen_algebraicFieldIndTopology_iff` only says *which sets* are ind-open (open traces on every
finite local subfield `F`); it gives no neighbourhood estimate uniform in `F`.  The missing input is
literally the reverse topology inclusion (`indCarrierBallNeighborhood_iff`), the tree supplies only
`ind ≤ norm`.

Moreover the missing input is **false** in the intended carrier: with a cofinal chain
`F_n = K(p^{1/2^n})` (value group `p^{ℤ/2^n}`), radii `r_n = p^{-n} ↓ 0`, and

  `U_0 = B(z, r_0)`, `U_{n+1} = B(z, r_{n+1}) ∪ ⋃_{y ∈ U_n} B_{F_{n+1}}(y, δ_y)`,
  `0 < δ_y ≤ min(|y|, dist(y, F_n ∖ U_n))/2`,

one gets `U_{n+1} ∩ F_n = U_n` (so `φ := ⋃ U_n` is ind-open with `φ ∩ F_n = U_n`) and
`dist(z, F_n ∖ U_n) = p^{-(n+1)+1/2^{n+1}} → 0`, so no ball around `z` lies in `φ`.  This is a
research note in the module doc (not formalised here).

The same shape of argument suggests `R1JointContinuousActionMissing` itself may be false: for
`O = φ` the conjugates of `y ∈ V ∩ F_n` under `Gal(Θ/E)` reach fields of depth `M(n)` ≥ degree of
the Galois closure, and `φ` misses every value-group level outside `|F_{M(n)-1}^×|`.  The actionable
next step is therefore a **counterexample package**, not another continuity estimate.

## Verification

* `lake env lean tmp/sheaf/xif/paper/S1975JointContinuityActual.lean` → EXIT = 0
* olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1975JointContinuityActual.olean`
* import round-trip check: `tmp/sheaf/xif/paper/S1975ImportCheck.lean` → EXIT = 0
* `#print axioms` on all seven main declarations: only `propext`, `Classical.choice`, `Quot.sound`
* no `sorry`, `admit`, `axiom`, `True`/`PUnit` slot, empty type or arbitrary inhabitant
* the target `R1JointContinuousActionMissing v` is **not** asserted: it occurs only as the conclusion
  of the conditional `r1JointContinuous_of_ballNeighborhood`.
