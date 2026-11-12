# Kernel equality via Teichmuller: exact missing

## Actual inputs
- S2442InertiaAPI.lean: actual prime-to-p torsion inertia, normal, quotient (EXIT=0; SHA B3B2054A...; olean 4289FCB0...).
- S2442ResidueAction.lean: actual valuation subring automorphism, residue action, normal residue kernel (EXIT=0; SHA F5F37EF7...; olean EE3317CC...).

## Goal
  PadicResidueKernel p = PadicAbsoluteGaloisInertia p.
Both sides are actual normal subgroups. Need two inclusions.

## (A) Residue kernel subsete prime-to-p inertia
If sigma fixes the residue field pointwise, and u is a prime-to-p torsion unit, then sigma u and u have the same residue. Need:
  PadicPrimeToPTorsionReductionInjective : Prop := Function.Injective
    (fun u : PadicPrimeToPTorsion p => residue of u in PadicResidueField p).
This is the Teichmuller/no-prime-to-p-torsion-in-1+m statement: if x^n=1 with (n,p)=1 and x has residue 1, then x=1. A proof needs a p-adic logarithm/binomial argument in the valuation ring; Mathlib has no such lemma for the algebraic closure.
Given this injectivity, the inclusion is formal: sigma fixes residue u, so u and sigma u have equal reduction; injectivity gives sigma u=u.

## (B) Prime-to-p inertia subset residue kernel
If sigma fixes every prime-to-p torsion unit, then sigma fixes the residue field. Need:
  PadicResidueTeichmullerLiftSurjective : Prop := every nonzero residue element is the reduction of a prime-to-p torsion unit.
This is Teichmuller lift/existence of roots of unity representatives in the valuation ring. Mathlib/tree has no Teichmuller lift API.
Given this surjectivity, the inclusion is formal: every residue element is reduce(u); sigma fixes u, hence fixes reduce(u); additivity fixes 0.

## Conditional assembly (not compiled)
If both Props are proved, then
  PadicResidueKernelEqualsInertia p
follows by Subgroup.ext and the two inclusion arguments above. No such theorem is added now; the Props are not inhabited.

## Surjectivity / Frobenius
PadicResidueActionSurjective needs identification of PadicResidueField with algebraic closure of ZMod p and lift of Frobenius to Qpbar. A Frobenius lift sigma and closure{sigma}=top are still missing. No fake lift is constructed.

## Status
No new Lean file compiled; no build/cache. Exact first missing:
1. reduction injective on prime-to-p torsion (Teichmuller);
2. every residue element is a prime-to-p torsion reduction (Teichmuller lift);
3. residue action surjectivity/Frobenius lift.
No fake/interface data labeled actual.