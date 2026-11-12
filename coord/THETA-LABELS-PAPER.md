# THETA-LABELS-PAPER — ivLabels vs litLabels and paper semantics (A1028)

Status: read-only source audit (lana root tree + coord excerpts); no compile.

## 1. `ThetaRegion.lean:34-74` definitions

- Capsule: `S_{j+1} = {0, ..., j}`, `j = i+1` (`ThetaRegion.lean:31-32`).
- Theta value: `q_{v_l}^{j²}` in the `l`-th tensor factor (`scaleEltAt`,
  `ThetaRegion.lean:34-36,126-132`); `q_v` is the `2ℓ`-th root of the Tate
  parameter (IUT I, Example 3.2(iv)); `1` at good places.
- (Ind2): independent `ℤ_p`-linear automorphisms of each factor log-shell,
  tensor-producted (`LocalTheory.indAut`, `LocalConstruct.tensorAut`),
  containing the image of `Ism` and larger; smaller than arbitrary
  automorphisms preserving the tensor (documented :40-46).
- (Ind1): automorphisms of the factors (already in Ind2) and **permutations of
  the labels of `S_{j+1}`**, moving the theta value to any label (`:47-48`).
- For a set `S i ⊆ S_{j+1}`:
  `Θ_{i,p} := ∏_c ⋃_{φ ∈ indAut} φ(⋃_{l ∈ S i} q_{v_l}^{j²}·⊗_l 𝓘_{v_l})`
  (`thetaFiniteOn`, :50-52); arch analog `LocalTheory.thetaInfinite` (:53-56).

Two readings (`:58-74`):
| name | definition | source line | meaning |
|---|---|---|---|
| `ivLabels i` | `{distinguished n i}` = `{j}` | `:236-237` | IUT IV, proof of Thm 1.10, Steps (iv)-(v); uses theta value at label `j` only |
| `litLabels i` | `Set.univ` = all `S_{j+1}` | `:239-241` | literal IUT III, Cor 3.12; includes label permutations of (Ind1) |

- `ivLabels_nonempty`, `litLabels_nonempty` (:243-246); `ivLabels ⊆ litLabels` (:248-249).
- `thetaFinite` / `thetaComponent` are the **iv** versions:
  `thetaFinite := thetaFiniteOn n i (ivLabels n i)`, `thetaComponent :=
  `thetaComponentOn n i (ivLabels n i)` (:251-259); `thetaPilot := thetaPilotOn n (ivLabels n)`
  (:315-316).
- Literal region is larger: `Cor312VariantHolds → Cor312LiteralHolds`
  (`cor312Literal_of_variant`, `Iut/Concrete/Literal.lean`), not conversely
  (:63-67). IUT IV's reading agrees with literal up to (Ind1) because label
  permutations preserve weights and volume (`:68-72`).
- Key difference (:73-74): the literal union hull is governed by
  `min_l ord_p(q_{v_l})`, not the average; the iv single-label reading cannot
  use that min.

## 2. Coord excerpts

`coord/ALPHA-DERIVATION.md` (A1013) records exactly this:
- capsule labels `S_{j+1}` and `q_{v_l}^{j²}`, `q_v` = 2ℓ-th root (`ThetaRegion:34-36`);
- `ivLabels` vs `litLabels` and `min_l ord` at `ThetaRegion:58-74`;
- literal single-label alpha `j²`, while the literal hull min can reduce the
  effective label to the smallest `ord_p(q)` (the most favorable), so iv and
  literal differ in the per-capsule coefficient.

`coord/ABC-ROUTES-SCREEN.md:116` records `ind2Term = frac(j² v_p(q)/(2ℓ))log p`
as a paper-level derivation (not lana-proved), consistent with the `j²`
label scaling.

## 3. `concreteVariantData`: which reading?

- `concreteVariantData` (`ThetaRegion.lean:359-362`):
  `{ data := D, qPilot := D.qPilot, rhsData := D.rhsData }`.
- `rhsData` (`:333-336`) = `D.rhsDataOn (ivLabels _) (ivLabels_nonempty _)` —
  **iv reading** (IUT IV's `−|log Θ|` with theta value at label `j`).
- `rhsDataLit` (`:338-341`) = `rhsDataOn (litLabels _)` — literal reading.
- `concreteVariantDataLit` (`:367-370`) uses `rhsDataLit`.

So our `SSIneq`/Cor312 target `Corollary312Variant (concreteVariantData D)` is
**iv reading**, not literal.  The literal statement is stronger and is implied by
the iv one; all lana formulas (`thetaComponent`, `gap`, `ind2Term`, hull volume
`V`) in the current tree are built on `thetaComponent` = iv, hence they compute
the iv R, not the literal R.

## 4. Consequences for our chain

- `V = logVol(hull(vcI))` uses `vcI` from the shell container (unscaled), while
  the theta-pilot region `thetaHull` in `RHSData` is `D.rhsData` = iv; the
  `gap`/`rhsData` formulas are iv.
- If we ever need the literal paper Cor 3.12, replace `rhsData` by
  `rhsDataLit`; the hull volume and per-capsule coefficients change (min_l vs
  distinguished label), so `M = A − R` changes.  Do not mix iv R with lit
  volume.
- The `ivLabels` reading is the one matching IUT IV Steps (iv)-(v) and the
  `concreteVariantData` used by `SSIneq`; it is the target relevant to our
  earlier `M` formulas.

## 5. Conclusion

- Paper θ-pilot hull has **two formal readings**: literal full `S_{j+1}`
  (`litLabels`) and IUT IV single label `{j}` (`ivLabels`).
- The repo's default `concreteVariantData`/`rhsData`/`thetaComponent` is the
  **iv** reading; `concreteVariantDataLit`/`rhsDataLit` is the literal one.
- Literal is stronger (iv ⇒ lit); the literal hull is governed by
  `min_l ord_p(q_{v_l})`, so iv vs lit changes the hull/volume and per-capsule
  coefficients.
- Our `V/gap/R` formulas use iv; any literal claim needs the `rhsDataLit`
  variant and a separate comparison.