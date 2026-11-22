# S2000: the actual cohomological Psi_cns and the exact first missing

Date: 2026-11-01.  File: `tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.lean`.
Consumer: `tmp/sheaf/xif/paper/_S2000Consumer.lean`.

## Outcome

**The actual local-field cohomological side is constructed; the paper-level
[AbsTopIII] Cor 1.10(b) group-theoretic algorithm remains the first missing.**

The file does **not** claim to construct the paper's `Psi_cns(G_v)`.  It
constructs, kernel-checked, the actual coefficient cyclotome, the actual direct
limit of continuous first cohomology over the open subgroups of
`G_v = Gal(Qbar_p/Q_p)`, and the actual Kummer map from the nonzero integral
monoid `O^tri` into that limit.  It also proves the unit part of the Kummer map
is injective and gives an unconditional isomorphism onto its image.  Nothing in
the file is a fake monoid, empty type, arbitrary inhabitant, axiom, or sorry.

## Constructed (EXIT = 0)

1. `PsiCnsCyclotome p = Hom(Q/Z, (O^tri)^times)`, the actual cyclotome, and
   `PsiCnsCyclotomeTorsionEquiv p : PsiCnsCyclotome p ~= Hom(Q/Z, torsion
   (O^tri)^times)`.  Thus the coefficient is the genuine `Hom(Q/Z, mu)`
   cyclotome, not a larger unit group.
2. `PsiCnsCoefficientAction p`, the actual continuous `G_v`-action on the
   cyclotome, and `PsiCnsCohomology p = lim_J H^1(J, PsiCnsCyclotome p)`, the
   genuine direct limit of continuous first cohomology over the open subgroups
   (`Iut.Foundations.ContinuousH1`).
3. `PsiCnsKummer p : O^tri -> PsiCnsCohomology p`, the actual Kummer map on
   **all** nonzero integral elements, not only units.  It is built from the
   canonical compatible rational root system in the Grothendieck group and the
   actual integral-unit root-ratio cocycle; `PsiCnsKummerGerm_mul` and
   `PsiCnsKummerGerm_one` prove it is a monoid homomorphism.  Its image
   `PsiCnsKummerImage p` is an actual submonoid of the cohomology limit.
4. `PsiCnsUnitKummer p`, the unit restriction, is **injective**
   (`PsiCnsUnitKummer_injective`), and
   `PsiCnsUnitKummerEquiv p : (O^tri)^times ~= PsiCnsUnitKummerImage p` is an
   unconditional multiplicative identification of the unit part.
5. `PsiCnsCyclotomeTorsionEquiv`, `PsiCnsKummerGerm_mul`,
   `PsiCnsUnitKummer_injective`, `PsiCnsUnitKummerEquiv`,
   `PsiCnsKummer_injective_of_kernelInUnits`, and
   `PsiCnsKummerKernelInUnits_iff_injective` use only
   `propext`, `Classical.choice`, and `Quot.sound`.

## Exact first missing

The first missing object is the [AbsTopIII], Corollary 1.10, (b), **functorial
group-theoretic algorithm** producing

  `mu_Q/Z(G_v) = colim_H (H^ab)_tors`,
  `mu_hat^Z(G_v) = Hom(Q/Z, mu_Q/Z(G_v))`,

the `H^2(G_v, mu_hat^Z(G_v)) ~= Z-hat` normalization, and the resulting
surjection `H^1(G_v, mu_hat^Z(G_v)) -> Z-hat`, together with the comparison of
this abstract cyclotome with the actual cyclotome `PsiCnsCyclotome p` and of
the inverse image of the nonnegative part with the Kummer image.  This is
exactly the paper's functorial group-theoretic construction of
`Psi_cns(G_v)`; it is not represented by any Lean declaration in this file,
and no fake interface is introduced for it.

For the **actual model**, the concrete statement that remains unproved is

  `PsiCnsKummerKernelInUnits p`:
  every element of the Grothendieck group `Qbar_p^times` with trivial
  Kummer germ is already a unit of `O^tri`.

The file proves this statement is **equivalent** to full injectivity of the
actual Kummer map
(`PsiCnsKummerKernelInUnits_iff_injective`), and that full injectivity gives
the monoid identification
`PsiCnsKummerImage p ~= PsiCnsModel p`
(`PsiCnsKummerImage_equiv_of_kernelInUnits`).  The statement itself is not
proved.  The natural proof route is the fixed-root argument plus the discrete
valuation of the finite fixed field (or the Eisenstein/norm argument); that is
the next executable step.

The `G_v`-action on the cohomological limit and its joint continuity are not
constructed here.  The pointwise action on the `IndIntegralMonoid` model and
the exact joint-continuity statement remain those of S1973
(`PsiCnsJointContinuousActionMissing`) and S1975
(`IndCarrierBallNeighborhood`).  The paper's `F_l^star`-symmetrizing label
isomorphisms also remain from S1973.

## Evidence

* target SHA256:
  `FAB1B252FF2C4E067AB86D6FC337DCD6A526018C8A003CDC92EC1957CFC0EDFB`
* EXIT = 0:
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.olean tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.lean`
* olean: 496,488 bytes, SHA256
  `1A037A3974C00A511A5E18583638AEE53A3DFAC93ED0562B805DDAE7BA0684C5`
* axioms: `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`,
  no custom axiom (checked by the file's `#print axioms`).
* consumer: `tmp/sheaf/xif/paper/_S2000Consumer.lean`, EXIT = 0, olean
  3,008 bytes, SHA256
  `3245653228795D5D36993B67C6752DD04D6BBC5A1E7EE05F88E833934FE1AF93`.
  The consumer checks the Kummer map, the unit isomorphism, the missing
  statement, and the conditional monoid identification.

## Not run

Full Project build, target comparator, independent review, and the
[AbsTopIII] group-theoretic construction itself.

## Next executable step

Prove `PsiCnsKummerKernelInUnits p` (equivalently full injectivity of
`PsiCnsKummer p`).  A concrete route is: generalize
`fixed_roots_of_integralUnitKummer_eq_one` from units to all of `O^tri`;
transport the resulting roots into the finite fixed field of the open subgroup;
and use the discrete valuation (or the Eisenstein irreducibility of
`X^n - p`) to show a nonunit integral element cannot be divisible in every
positive degree.  After that, the remaining source-level gap is exactly the
[AbsTopIII] Cor 1.10(b) group-theoretic cyclotome/H^2 algorithm and its
comparison with `PsiCnsCyclotome p`.
