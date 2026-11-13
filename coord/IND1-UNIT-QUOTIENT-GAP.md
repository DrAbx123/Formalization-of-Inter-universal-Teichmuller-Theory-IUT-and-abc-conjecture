# Ind1 from actual unit quotient: generic lemma and exact source gap

Date: 2026-11-14. Owner: stepxi. Status: generic unit-quotient log-image lemma written; nonidentity source-arrow test blocked at the documented DPrimeStrip source gap (no topology/integral units in the abstract layer).

## Landed Lean (compile pending/available)

`tmp/sheaf/xif/paper/Mzk1Ind1LogLatticeActionActual.lean`:
- `SinglePlaceLogLatticeAction e he` built from:
  - `integralUnitMap e he` (actual unit map),
  - `unitPerfectionMap e he` (rationalization),
  - `unitPerfectionMap_log_commute` (square with `unitLogPerfectionEquiv`),
  - `map_mem_integralLogShell` (integral log-shell preservation).
- Theorems `singlePlace_unitLog_map`, `singlePlace_shellPreserve`.

`tmp/sheaf/xif/paper/Mzk1Ind1UnitQuotientActual.lean`:
- `unitLogQuotientEquivOfMulEquiv β`:
  from a unit-torsion-quotient action
  `β : U_F/tors ≃* U_{F'}/tors`
  build the actual log-image action
  `(unitLogHom F).range ≃* (unitLogHom F').range`
  via `unitLogTorsionQuotientEquivRange`.
- `unitLogQuotientEquivOfMulEquiv_apply` (definitional formula).
- `unitPerfectionMap_log_square`, `unitLog_map_mem_integralLogShell`.

## What is genuinely supplied

1. Unit group / torsion quotient: `unitLogTorsionQuotientEquivRange`, `unitLogTorsionQuotientHomeomorph`.
2. Actual field isometry action: `integralUnitMap`, `unitPerfectionMap`, square `unitPerfectionMap_log_commute`.
3. Lattice preservation: `map_mem_integralLogShell`, hence a single-place real lattice action for isometry-induced arrows.
4. Generic quotient action: an arbitrary `β : U_F/tors ≃* U_{F'}/tors` gives an actual log-image `MulEquiv`, with no arbitrary linear equivalence.

## Exact source gap for a nonidentity arrow test

The abstract `DPrimeStrip`/`DPrimeStripEquiv` layer provides only the algebraic group, projections, and group isomorphism; it has no topology, integral units, local reciprocity, or reconstruction algorithm. Therefore it does NOT by itself yield a continuous
`β_a : U_F/tors → U_{F'}/tors`.
To finish the paper Ind1 one still needs the actual arithmetic realization:
- identify the source monoid units with actual `O_F^×` or `W_F`;
- use the actual `FPrimeStrip` arrow `isoMon` and `TimesMuQuotient.congr` to get `β_a`;
- prove continuity on the original quotient topology (or descend Galois-invariants via `baseUnitsGaloisFixedEquiv`);
- verify the log-lattice square and compound/inverse/tensor laws.

This node is absent from the checked source files; no unconditional inhabitant was found. Do not fill it with `Nonempty` or an arbitrary same-dimension linear equivalence.

## Consumer contract

- Isometry-induced arrows: use `SinglePlaceLogLatticeAction` and `singlePlace_shellPreserve`.
- General Ind1: pass the actual continuous `β_a` to `unitLogQuotientEquivOfMulEquiv`; then rationalize and promote to `ℚ_[p]`-linear only after proving continuity (`continuous_ratLinearMap_padic_smul`).
- Until `β_a` is supplied, `Ind1ShellTransportForRequired places e φ` remains the exact consumer input.
