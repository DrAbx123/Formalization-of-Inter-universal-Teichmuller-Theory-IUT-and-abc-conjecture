# S2016: (M7) proved — `G_v`-equivariance of the actual Kummer map

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S2016KummerEquivarianceActual.lean.
Consumer: S2011 (tmp/sheaf/xif/paper/S2011Cor110bActual.lean), missing item (M7);
through it the [AbsTopIII] Cor 1.10 (d) comparison of S2000
(tmp/sheaf/xif/paper/S2000CohomologicalPsiCnsActual.lean).

## Outcome

**S2011 missing item (M7) is proved, unconditionally.**  For every prime p,
every `g in G_v = Gal(Qbar_p/Q_p)` and every nonzero integral `a`,

    PsiCnsKummer p (g . a) = germAction p g (PsiCnsKummer p a),

where `g . a = LocalIntegralMonoid.galoisAction p g a` is the genuine Galois
action on the actual nonzero integral closure of the valuation ring of `Q_p`
inside `Qbar_p`, `PsiCnsKummer p : O^tri -> lim_J H^1(J, mu_hat^Z)` is the
actual Kummer map of S2000, and `germAction p` is the `G_v`-action on the
actual cohomological limit constructed in S2011.

No new interface, no axiom, no sorry, no added hypothesis.  This is exactly the
statement S2011 recorded as missing, proved along the route S2011 recorded.

## Constructed (EXIT = 0)

* `monoAction`, `monoGroupAction`, `monoUnitAction`: the mono-analytic
  `G_v`-action on `O^tri`, on its Grothendieck groupification, and on the
  integral units, together with their cocycle laws
  (`monoAction_mul_apply`, `monoGroupAction_mul_apply`,
  `monoGroupAction_of`, `unitGrothendieck_monoUnitAction`,
  `coefficientAction_act_apply`: the coefficient action of S2011 is the unit
  action evaluated pointwise).
* `transportRealization`: **the transported root realization.**  For a root
  realization `R` of `a` over an open subgroup `U` fixing `a`, and
  `g in G_v`, the realization of `g . a` over the conjugated open subgroup
  `g U g^{-1}` whose root system is the `g`-translate of the root system of
  `R` in the Grothendieck group and whose integral-unit ratio is
  `g . (ratio of the conjugate element)`.  Its `fixed` field is the action law
  plus `k = g^{-1} h g`; its `ratio_spec` is the cocycle law of the
  groupification action, i.e. the ratio cocycle of the transported system is
  exactly the translate of the ratio cocycle of `R`.
* `transportRealization_germ`: on the common open domain `g U g^{-1}` the
  transported cocycle and the translate `x |--> g . c(g^{-1} x g)` of
  `translateRep p g R.representative` agree pointwise, so the germs agree
  (identity coboundary).
* `transportRealization_canonical_germ`: the canonical realization of `g . a`
  and the transported canonical realization of `a` have the same germ, by
  `IntegralKummerRootRealization.germ_eq` (root-choice independence).  This is
  the step that removes the chosen compatible root system.
* `PsiCnsKummer_equivariant`: **M7**.
* `PsiCnsKummer_galoisAction`: the same statement with the literal
  `LocalIntegralMonoid.galoisAction`.
* `germAction_mem_kummerImage`: the actual Kummer image of `O^tri` is stable
  under the `G_v`-action on the limit.

## Proof chain

```
PsiCnsKummer p (g . a) = (canonical realization of g . a).germ   [rfl]
                       = (transport of canonical realization of a).germ
                                                          [IntegralKummerRootRealization.germ_eq]
                       = translateGerm p g (realization of a).germ
                                                          [transportRealization_germ]
                       = translateGerm p g (PsiCnsKummer p a)   [rfl]
                       = germAction p g (PsiCnsKummer p a)      [germAction_apply]
```

## Evidence

* source 333 lines / 14,771 bytes, SHA256
  FC61C9832E3B6BD1EF03170A5F169948B452016699D79F41CF3BD23C973036E9;
  `lake env lean -j1 -o ...` EXIT = 0, 0 errors, 0 warnings
  (log: tmp/sheaf/xif/paper/S2016Compile.log).
* olean 491,664 bytes, SHA256
  940CB1D535424EC6D1FF4D4C131D0552C20443757FEAAE1E0CB0DC9D17BA8013.
* axioms: propext, Classical.choice, Quot.sound only (file prints, consumer
  re-checks).  No sorryAx anywhere.
* consumer _S2016Consumer.lean: EXIT = 0, olean 2,768 bytes, SHA256
  5D205868A8B5993BFF872F05B414DA7F0F54DEC69D3D0FE1BC7494C4F64F6010.  It
  re-checks the literal statement on the carriers, the `galoisAction` form,
  the compatibility with the group law
  (`PsiCnsKummer p (g . (h . a)) = germAction p g (PsiCnsKummer p (h . a))`),
  and the image-stability corollary.

## Status of the other S2011 gaps (unchanged)

(M1) transfer/Verlagerung and the colimit `colim_H (H^ab)_tors`; (M2) local
reciprocity on torsion; (M3) continuous `H^2` and `H^2(G_v, mu_hat^Z) = Z-hat`;
(M4) the normalized surjection `H^1(G_v, mu_hat^Z) ->> Z-hat` (on the tree only
the weakened `weakFrobeniusNormalization`); (M5) joint continuity (no topology
on the limit); (M6) the `O^tri_{Qbar_p}` versus `k_v^times` model caveat.
M7 is now closed; it does not close the (d) comparison, which still needs (M3)
and (M4).

## Not run

Full Project build, target comparator, independent review, and the [AbsTopIII]
group-theoretic construction itself.

## Next executable step

(1) transfer/Verlagerung for finite-index open subgroups (prerequisite for
stating (M1)-(M4)); or (2) the levelwise torsion reciprocity (M2) on the tree's
carriers; or (3) with M7 available, the `G_v`-equivariant form of (M4) is the
natural intermediate: a normalizing homomorphism that is equivariant for the
action on the limit and the cyclotomic character on the target.
