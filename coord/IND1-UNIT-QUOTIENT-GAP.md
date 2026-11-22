# Ind1 from actual unit quotient: algebraic core and exact source gap

Date: 2026-11-14 (corrected). Owner: stepxi.

Status: algebraic unit-quotient core and isometry-induced log-lattice action implemented; the ONLY remaining source gap is the actual identification of the source unit quotient with `(Integers F)ˣ/tors` and the derivation of `β_a` from the actual source action.  Continuity of such a `β_a` is NOT a new source node once that identification is made (see §A).

## A. Continuity correction (supersedes the earlier wild-hom claim)

For the standard topology on finite-rank `(ℤ_[p])^d`, any additive group homomorphism
`f : (ℤ_[p])^d →+ (ℤ_[p])^{d'}` is automatically continuous:

- `p^n` is an integer, so additivity gives `f (p^n • x) = p^n • f x`;
- hence `f (p^n B_d) ⊆ p^n B_{d'}`;
- the subgroups `p^n B` form a neighbourhood basis of `0`, so `f` is continuous at `0`;
- an additive map continuous at `0` is continuous everywhere.

Therefore, after `W_F` is identified with a finite-rank `ℤ_p`-module/adic torus, any abstract group isomorphism `β_a : W_F → W_{F'}` (respecting the additive structure) is automatically continuous.  Do NOT add a free `Continuous β_a` field to the final theorem.

Target Lean lemma (not yet landed):
```lean
theorem continuous_of_addHom_fin_zpadic
    (f : (Fin d → ℤ_[p]) →+ (Fin d' → ℤ_[p])) : Continuous f
```
Proof plan: neighbourhood basis `p^n • ⊤`, `map_nsmul`/`map_zsmul`, `AddMonoidHom.continuous_of_continuousAt_zero`; then transport along the actual `AddEquiv W_F ≃ Fin d → ℤ_[p]`.

Once continuous, `continuous_ratLinearMap_padic_smul` promotes ℚ-linearity to ℚ_p-linearity.

## B. Algebraic core (landed/queued)

- `tmp/sheaf/xif/paper/Mzk1Ind1AlgebraicUnitQuotientActual.lean`:
  `fPrimeStripUnitQuotientEquiv a v : TimesMuQuotient ((F.Mon v)ˣ) ≃* TimesMuQuotient ((F'.Mon v)ˣ)`
  built from `isoMon` + torsion quotient.  This is the algebraic shape of `β_a`.
- `tmp/sheaf/xif/paper/Mzk1Ind1UnitQuotientActual.lean`:
  `unitLogQuotientEquivOfMulEquiv β` maps an abstract unit-quotient action to an actual log-image equivalence, using `unitLogTorsionQuotientEquivRange`.
- `tmp/sheaf/xif/paper/Mzk1Ind1LogLatticeActionActual.lean`:
  `SinglePlaceLogLatticeAction e he` from an actual isometric field map:
  `integralUnitMap`, `unitPerfectionMap`, `unitPerfectionMap_log_commute`, `map_mem_integralLogShell`.

## C. The only remaining source gap

The tree does NOT contain the actual identification
```text
TimesMuQuotient ((F.Mon v)ˣ)  ≃*  ((Integers F)ˣ ⧸ torsion)
```
nor a construction of `β_a` from the actual source procession action.

`FPrimeStripEquiv` fields are only `isoPi`, `isoG`, `isoMon`, `compatProj`, `compatAction`, `compatDegree`; all algebraic, and `F.Mon v` is an abstract CommMonoid, not `(Integers F)ˣ`.  `TimesMuQuotient` only quotients an abstract CommGroup by torsion.

Required new source nodes:
1. actual unit realization: identify `(F.Mon v)ˣ` (or the relevant source unit layer) with `(Integers F)ˣ` / `W_F`;
2. derive `β_a` on that layer from the actual source arrow (`isoMon`, `TimesMuQuotient.congr`, Galois descent as needed);
3. prove the log-lattice square with `sourceLocalLogShellDatum`;
4. compound/inverse/tensor laws.

No extra continuity node is needed after step 1 (see §A).

## D. §7.5 Kummer finite layer: only an injection is present

`LeanFormal/IUT/IUTII/Kummer/KummerGaloisClass.lean` supplies:
- `kummerRatioHom` and `kummerMap : kummerRootSubgroup →* ((L ≃ₐ[K] L) →* rootsOfUnity n L)`;
- `kummerMap_eq_one_iff`: kernel = `n`-th powers in `Kˣ`;
- `kummer_pow_mem_of_trivial`.

It does NOT supply:
- `kummerRootSubgroup = ⊤` for all local units in a chosen finite extension;
- H¹ surjectivity / inverse map on `U_F/U_F^{p^n}`;
- compatibility in `n` or an inverse-limit/torsion-quotient construction.

Thus the Kummer route gives an injection layer only; H¹ surjectivity and finite-layer compatibility are new source nodes.

## E. §7.2 inertia-image route

No existing unconditional donor for `I_F → G_F^{ab}` image plus local reciprocity on the actual FPrimeStrip units was found.  This is a new source node, not an existing theorem.

## F. Consumer rule

- Isometry-induced arrows: use `SinglePlaceLogLatticeAction` / `singlePlace_shellPreserve`.
- General Ind1: first prove the actual unit identification (§C), build `β_a`, then use `unitLogQuotientEquivOfMulEquiv`; continuity is automatic by §A once `β_a` is an additive endomorphism of a finite-rank `ℤ_p`-module.
- Until §C is supplied, `Ind1ShellTransportForRequired places e φ` remains the exact consumer input.  Do not fill it with `LinearEquiv.refl` or an arbitrary same-dimension equivalence.

## Target Lean lemma status: continuous_of_addHom_fin_zpadic

Not yet landed.  Planned proof:
1. choose `n` with `(p:ℝ)^(-n) < ε` (geometric decay);
2. for `x : (Fin d → ℤ_[p])`, if `‖x i‖ < (p:ℝ)^(-n)` then `x i ∈ span (p^(n+1))` by `PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one` / `norm_le_pow_iff_mem_span_pow`;
3. write `x = (p^(n+1) : ℤ) • c` pointwise and use `map_nsmul` of the additive hom plus `Ideal.isOpen_pow_of_isMaximal` for the `p^n`-neighbourhood basis;
4. conclude `ContinuousAt f 0` and then `Continuous f` via `AddMonoidHom.continuous_of_continuousAt_zero`.

No sorry/axiom placeholder is put in the tree.  Until this lemma lands, the §7.1 continuity statement remains a proof target, not a formalized theorem.

## Actual donor discrepancy (2026-11-14)

Checked the actual FPrimeStrip units:
- `LeanFormal/IUT/IUTI/HodgeTheater/PrimeStripCore.lean:118-120`: `FPrimeStrip.Mon : V → Type v` is an abstract CommMonoid with an action and degree; no identification with `(Integers F)ˣ`.
- `LeanFormal/IUT/IUTII/Frobenioid/LocalPrimeStrip.lean:41`: the concrete local FPrimeStrip has
  `Mon v = (AlgebraicClosure ℚ_[v.1])ˣ`,
  not `(Integers F)ˣ`; it is an algebraic-closure unit group, not the completion integral-unit group.
- `TimesMuQuotient U = U ⧸ CommGroup.torsion U` (Kummer/TimesMuQuotient.lean:24) only quotients the abstract group by torsion.

Therefore there is no existing identification
`TimesMuQuotient ((F.Mon v)ˣ) ≃* ((Integers F)ˣ ⧸ torsion)`.
The source construction node must first identify the actual local integral-unit layer (`(Integers F)ˣ` or `W_F`) inside/along the source FPrimeStrip unit layer; the current `F.Mon v = (AlgebraicClosure ...)ˣ` is a different object.  The `fPrimeStripUnitQuotientEquiv` of Mzk1Ind1AlgebraicUnitQuotientActual is only the algebraic shape on the abstract `F.Mon` layer.

No fake identification/β_a is added.

## Actual local Mon instance and the exact comparison target (2026-11-14)

Implemented in `tmp/sheaf/xif/paper/Mzk1Ind1LocalMonActual.lean`:
- `localFPrimeStrip_Mon_eq (v) : localFPrimeStrip.Mon v = (AlgebraicClosure ℚ_[v.1])ˣ` (rfl);
- `LocalUnitQuotient v := TimesMuQuotient (localFPrimeStrip.Mon v)`, i.e. the algebraic-closure unit group modulo torsion;
- `localFPrimeStrip_reflUnitQuotientEquiv v`, the actual `fPrimeStripUnitQuotientEquiv` at the `localFPrimeStrip` instance (algebraic `isoMon` layer).

### Exact comparison target/obstacle

The actual source Mon in this instance is
`(AlgebraicClosure ℚ_[v.1])ˣ`, while the desired local unit quotient is
`((Integers F)ˣ ⧸ torsion)` for a finite local field extension `F/ℚ_[p]`.

These are NOT the same group quotient:
- `(AlgebraicClosure ℚ_[p])ˣ` contains all roots of unity and has infinite-rank/torsion-free quotient behaviour;
- `(Integers F)ˣ` for a finite extension is a finitely generated (compact) unit group, so its torsion quotient is finitely generated.

The natural comparison is an actual **map**
`(Integers F)ˣ → (AlgebraicClosure ℚ_[p])ˣ` (via `algebraMap F (AlgebraicClosure)`)
composed with torsion quotients, not a canonical isomorphism.  It is not surjective and its cokernel contains the non-integral algebraic-closure units.

Therefore no fake `≃*` is added.  The source node remains:
1. identify the actual local integral-unit layer inside the source unit layer;
2. construct the actual Ind1/Ind2 action on that layer;
3. use the resulting map, not an arbitrary isomorphism, as `β_a`.

## Green probes and self-identification (2026-11-14)

Green with only `[propext, Classical.choice, Quot.sound]` (no sorryAx):
- `localFPrimeStrip_Mon_eq` (Mzk1Ind1LocalMonActual);
- `integerUnitsRingHom_injective`, `integersUnitsToAlgClosure_injective` (Mzk1Ind1IntegralUnitMapActual);
- `sourceUnitLogRangeEquiv_apply`, `sourceUnitQuotientIdentification_self_nonempty` (Mzk1Ind1SourceUnitBridgeActual).

The inhabitant `sourceUnitQuotientIdentification_self` takes `W = ((Integers K)ˣ ⧸ torsion)` and uses `MulEquiv.refl`. It is an interface-consistency check only, NOT the actual source W identification. The source W identity is still absent:
- the concrete local FPrimeStrip Mon is `(AlgebraicClosure ℚ_[p])ˣ`;
- the target integral-unit quotient is `((Integers K)ˣ ⧸ torsion)`;
- the natural map induced by `Integers K → AlgebraicClosure K` is injective but not surjective, and the torsion quotients have different algebraic size;
- no isomorphism is added.

## New actual source unit layer from integral units (2026-11-14)

Instead of forcing the algebraic-closure unit group to be the source W, we define the actual source unit layer directly:

```lean
abbrev ActualSourceUnitLayer (K) := (Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ

def actualSourceUnitLayer_self (K) :
    SourceUnitQuotientIdentification (ActualSourceUnitLayer K) K where
  equiv := MulEquiv.refl _
```

This file also provides
`actualSourceUnitLogRangeEquiv (β : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer L) : logRange K ≃* logRange L`.

So the remaining source node is exactly the actual Ind1/Ind2 action
`β : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer L` derived from the
procession action.  The previous algebraic-closure `F.Mon` is NOT identified
with this layer; it remains a separate donor layer.  No fake iso is added.
# Exact Ind1 unit-action interface (2026-11-14)

Added in Mzk1Ind1ActualSourceUnitLayerActual:

```lean
structure ActualInd1UnitAction (K) (L) where
  beta : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer L
  fromProcession : Prop

def ActualInd1UnitActionRequired (K) (L) : Prop := Nonempty (ActualInd1UnitAction K L)

def actualInd1LogRangeEquiv (A : ActualInd1UnitAction K L) :
    (unitLogHom K).range ≃* (unitLogHom L).range :=
  actualSourceUnitLogRangeEquiv A.beta
```

The structure has NO inhabitant. The remaining source task is exactly to construct
`beta : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer L` from the actual Ind1/Ind2
procession action and prove its `fromProcession` provenance. The previous
FPrimeStrip.isoMon acts on the algebraic-closure `F.Mon` layer, not on the
integral-unit quotient; no fake identification is added.
