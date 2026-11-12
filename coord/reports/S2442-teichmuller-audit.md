# Teichmuller lift / prime-to-p injectivity: exact missing

## Actual baseline
- S2442InertiaAPI.lean: actual prime-to-p torsion inertia/normal/quotient (EXIT=0; SHA B3B2054A...; olean 4289FCB0...).
- S2442ResidueAction.lean: actual residue action and normal residue kernel (EXIT=0; SHA F5F37EF7...; olean EE3317CC...).

## (1) Teichmuller lift on PadicResidueField
Mathlib has Henselian/Teichmuller APIs:
- `HenselianRing`/`HenselianLocalRing` (RingTheory.Henselian),
- `IsAdicComplete.henselianRing`,
- `RingTheory.Teichmuller` for adic complete rings (teichmullerFun/teichmuller).
However `PadicValuationSubring p` is the valuation ring of the algebraic closure, not the p-adic completion. No instance/proof is present that it is adic complete or HenselianLocalRing; the complete object `PadicComplexInt p` is a different ring and there is no map from its Teichmuller representatives into `PadicAlgCl`.
Exact missing lemma:
  PadicTeichmullerLift : Prop := forall x : PadicResidueField p,
    exists u : PadicValuationSubring p, residue u = x and u is a unit and
      exists n, n.Coprime p and u^n = 1.
No inhabitant was constructed.

## (2) Prime-to-p reduction injectivity
Needed:
  PadicPrimeToPTorsionReductionInjective : Prop := Function.Injective
    (fun u : PadicPrimeToPTorsion p => residue (PadicValuationSubring p) u).
Equivalent form: if u^n=1, n coprime p, and residue u=1, then u=1. A proof needs the
p-adic logarithm/binomial argument on the valuation ring: the leading term n(u-1) has the same
valuation as u-1 because p does not divide n, contradiction unless u=1. That valuation/binomial
API is not present for PadicAlgCl. No proof or counterexample was obtained.

## (3) Kernel assembly
Given Teichmuller lift and reduction injectivity, the two inclusions are formal:
- residue-kernel subset inertia: sigma fixes residue, so u and sigma u have equal reduction; injectivity.
- inertia subset residue-kernel: every residue element is a reduction of prime-to-p torsion; sigma fixes it.
Then Subgroup.ext gives PadicResidueKernel=PadicAbsoluteGaloisInertia. Neither input is inhabited, so equality remains missing.

## Surjectivity/Frobenius
Residue action surjectivity additionally needs identification PadicResidueField ~= algebraic closure of ZMod p and a Frobenius lift to PadicAlgCl; still missing. PadicInertiaQuotientProcyclic remains a Prop.

## Status
No new Lean file compiled; no build/cache. No fake Hensel/Teichmuller inhabitant. Exact first missing: Teichmuller lift + prime-to-p reduction injectivity (and then residue surjectivity/Frobenius).