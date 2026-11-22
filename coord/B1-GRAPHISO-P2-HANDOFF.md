# B1 GraphIso P2 handoff (emmy lane, 2026-11-17 20:32)

Status: all algebra is in place; only the two-sided AlgEquiv assembly remains, and the compile is
currently blocked by toolchain-level olean read failures (infrastructure), not by mathematics.
This page is the exact remaining to-do, with donor names.

## Target

In tmp/sheaf/xif/paper/Mzk1G1B1GraphIsoModelActual.lean (namespace
LeanFormal.IUT.XiFPaper.Mzk1G1B1GraphIsoModelActual), prove

    theorem graphIso_holds (h : Polynomial Q) :
        Mzk1G1B1SmoothCriterionSubmActual.GraphIso h

where (donor, DONE 11:15:00):

    GraphIso h : Prop :=
      Nonempty (smoothModelRing h ~=a[Polynomial Q] Localization.Away (hDerivElt h))
    smoothModelRing h :=
      MvPolynomial (Fin 2) (Polynomial Q) / Ideal.span (Set.range (smoothModelRel h))
    smoothModelRel h 0 = C lam - hAtT h          -- h(T)
    smoothModelRel h 1 = hDerivAtT h * Z - 1     -- h'(T) * Z = 1
    chartT h := MvPolynomial (Fin 1) Q           -- renamed t-line, avoids the double-Algebra diamond
    hDerivElt h : chartT h                       -- h'(t)

## Already proved in the file (do not redo)

hAtT_eq_aeval, pderiv_aeval_X0_derivative, hDerivAtT_eq_aeval, map_aeval_apply,
smoothModelEval_X0 - the three bridge identities (donor explicit Finset.sum forms vs
Polynomial.aeval) plus the Polynomial Q-linearity upgrade of the chartT -> smoothModelRing map.

## Remaining assembly (two-sided AlgEquiv.ofAlgHom; no ideal bookkeeping)

psi : smoothModelRing h ->a[Polynomial Q] Localization.Away (hDerivElt h)
  * Induced by MvPolynomial.aeval sending X 0 to the image of t and X 1 to
    IsLocalization.Away.invSelf hDerivElt; generator computations via smoothModelEval_X0 and
    hDerivAtT_eq_aeval.
  * Both relations map to zero: relation 0 by construction; relation 1 because
    h'(t) * (h'(t))^(-1) - 1 = 0 (IsLocalization.Away.mul_invSelf).

chi : Localization.Away (hDerivElt h) ->a[Polynomial Q] smoothModelRing h
  * IsLocalization.Away.lift with h'(t) mapped to the class of hDerivAtT h; the unit
    hypothesis is exactly Mzk1G1B1SmoothCriterionSubmActual.smoothModel_deriv_isUnit h.
  * t maps to the class of X 0 in smoothModelRing h.

psi_chi : psi o chi = id      -- IsLocalization.algHom_subsingleton
chi_psi : chi o psi = id      -- MvPolynomial.algHom_ext / AlgHom.ext on the two generators;
                                 for X 1 use mul_eq_one uniqueness of the inverse of h'(T).

Then AlgEquiv.ofAlgHom psi chi psi_chi chi_psi, wrapped in a Nonempty constructor.

## Reusable donors (checked; no duplicates in the tree)

* Mzk1G1B1GraphIsoActual (DONE 11:24:24): away_algEquiv_quotient,
  isLocalization_away_quotient, graphIso_lambda_side, away_algEquiv_quotient_of_chartT,
  isLocalization_away_quotient_of_chartT.
* Mzk1G1B1SmoothCriterionSubmActual (DONE 11:15:00): smoothModelRel, smoothModelRing,
  smoothModelPre, smoothModelPresentation, smoothModel_deriv_isUnit,
  smoothModel_relation_mem, chartT, hElt, hDerivElt, chartMap, algebraMap_eq, algebraMap_X,
  isSmoothAt_of_formallySmooth, smoothAt_of_derivative_notMem.
* Mathlib: Localization.awayEquivAdjoin (Away r ~=a[R] AdjoinRoot (C r * X - 1)),
  IsLocalization.adjoin_inv, IsLocalization.Away.lift, IsLocalization.algHom_subsingleton,
  AlgEquiv.ofAlgHom, MvPolynomial.aeval, MvPolynomial.renameEquiv, MvPolynomial.finSuccEquiv.
  Key fact: AdjoinRoot f is definitionally Polynomial R / Ideal.span {f} (this is why P1 was
  a one-liner).

## Reconnaissance note (no duplicate found)

The tree has no ring isomorphism Q[lam][T]/(lam - h(T)) ~= Q[t]: hPolyT and hPolyLam in
Mzk1G1PsiHPolyActual are *chart formulas*, not ring isomorphisms. Mzk1G1OmegaActual.
derivation_relation is the two-variable Fermat relation, unrelated to this main relation.
So P2 must be built here; nothing to port.

## What this unlocks

GraphIso h + smoothModel_formallySmooth + isSmoothAt_of_formallySmooth + hbridge_of_hcrit
give hbridge : Ram (chartMorphismInf h) subset derivativeZeroSet h; then
hbH_of_hbridge_and_out h hh hdeg hval hbridge (hout h hh hdeg) gives
Branch (hPoly h hh) subset boundarySetGlued - the hb consumed by the P8/G-K branch side.
hout is unconditional (DONE 10:32:11, Mzk1G1B1HoutActual).
