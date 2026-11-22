# S2006: the Kummer kernel of the actual Psi_cns lies in the integral units

Date: 2026-11-01.  File: `tmp/sheaf/xif/paper/S2006KummerKernelActual.lean`.
Consumer: `tmp/sheaf/xif/paper/_S2006Consumer.lean`.

## Outcome

**`PsiCnsKummerKernelInUnits p` is proved** for the actual local field, hence
also **full injectivity of `PsiCnsKummer p` on `O^tri`** and the unconditional
monoid identification `PsiCnsKummerImage p ~= PsiCnsModel p`.

The S2000 package had left `PsiCnsKummerKernelInUnits p` as its exact concrete
first missing statement.  It is now a theorem; nothing in it is assumed, and the
only axioms are `propext`, `Classical.choice`, `Quot.sound`.

## Constructed (EXIT = 0)

1. **The fixed field of an open subgroup is an actual nonarchimedean local
   field.**  For `U : OpenSubgroup (LocalAbsoluteGalois p)` the field
   `LocalIntegralUnitKummerInjectivity.FixedField p U` carries
   `FiniteDimensional Q_p`, `CompleteSpace`, `LocallyCompactSpace`, the
   valuative relation and topology of the restricted p-adic spectral norm
   (Mathlib's `PadicAlgCl` normed-field structure), `ValuativeRel.IsNontrivial`,
   and finally `IsNonarchimedeanLocalField`
   (`fixedFieldIsNonarchimedeanLocalField`).
2. **Fixed roots from equal Kummer classes** (`exists_fixed_ratio_root`).  If
   `PsiCnsKummer p a = PsiCnsKummer p b` for nonzero integral `a`, `b`, then on
   a common open subgroup `U` the two canonical root-ratio cocycles differ by an
   explicit integral-unit coboundary `d`.  With `Aroot^n = of a`,
   `Broot^n = of b` (in the actual Grothendieck group), the adjusted quotient
   `Q = (Broot / Aroot) / d` is fixed by `U` and satisfies `Q^n = of b / of a`
   for every `n > 0`.
3. **Kummer rigidity in the finite fixed field** (`fixedField_eq_one_of_roots`).
   The local-field rigidity theorem of
   `LeanFormal.IUT.IUTII.Kummer.LocalFieldRigidity` applied to the actual fixed
   field: a unit of a nonarchimedean local field admitting roots of every positive
   degree is one.
4. **The kernel-in-units theorem** (`PsiCnsKummerKernelInUnits_holds`).  Every
   Grothendieck-group element with trivial Kummer germ is a unit of `O^tri`.
   The proof transports the fixed roots into the fixed field, applies the
   rigidity theorem to `b / a`, and concludes `b = a`, hence `x = of a / of b = 1`.
5. **Corollaries.**  `PsiCnsKummer_injective : Function.Injective (PsiCnsKummer p)`
   and `PsiCnsKummerImage_equiv : Nonempty (PsiCnsKummerImage p ~= PsiCnsModel p)`,
   obtained from the S2000 equivalences.

## Evidence

* target SHA256 (`.lean`):
  `CAEC44A4F642D4E2EBE2ED613E231605AFA6B5CCA8074986E9C8168DA3B36499`
* EXIT = 0:
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2006KummerKernelActual.olean tmp/sheaf/xif/paper/S2006KummerKernelActual.lean`
* olean: 898,648 bytes, SHA256
  `0C38A070ACD53FCFDAF68557C31CEE6CA42EA08AB3A690978466A65839A65392`
* axioms: `propext`, `Classical.choice`, `Quot.sound` only, for
  `fixedFieldIsNonarchimedeanLocalField`, `fixedField_eq_one_of_roots`,
  `exists_fixed_ratio_root`, `fixedField_unit_of_fixed`,
  `PsiCnsKummerKernelInUnits_holds`, `PsiCnsKummer_injective`,
  `PsiCnsKummerImage_equiv`; no `sorryAx`, no custom axiom (checked by the
  file's `#print axioms`).
* consumer: `tmp/sheaf/xif/paper/_S2006Consumer.lean`, EXIT = 0, olean
  3,104 bytes, SHA256
  `B553CE65923BEE67FA51639FC5300D23D5869DF0AA856DEC4EB2B34146E21F7B`.
  It checks the kernel-in-units statement, full injectivity, the unconditional
  monoid identification, and the S2000 equivalence
  `PsiCnsKummerKernelInUnits p <-> Function.Injective (PsiCnsKummer p)`.

## Method notes

* The local-field structure on the fixed field is the genuine restricted p-adic
  spectral norm of the algebraic closure (`PadicAlgCl`), not an invented norm;
  local compactness uses finite dimensionality over the complete locally compact
  `Q_p`; the valuative topology is the norm topology, and the valuation is
  `NormedField.valuation`.
* The cocycle computation is done in the actual Grothendieck group: the unit
  reiation from the germ equivalence `ContinuousH1GermRepresentative.Equivalent`
  is pushed through `unitGrothendieckHom`, using `ratio_spec` and the
  equivariance `unitGrothendieckHom_action`.
* Pure abelian-group identities are discharged by transporting to `Additive`
  and `abel`; `group` is not used.

## Not run

Full Project build, target comparator, independent review, and the
[AbsTopIII] Corollary 1.10(b) group-theoretic cyclotome/`H^2` algorithm.

## Next executable step

The remaining source-level gap is exactly the S2000 one: the [AbsTopIII],
Corollary 1.10, (b), functorial group-theoretic construction of
`mu_hat^Z(G_v)`, its `H^2`-normalization, and the comparison of the abstract
`Psi_cns(G_v)` with the actual Kummer image (now identified with `O^tri`).
The `G_v`-action on the cohomological limit and its joint continuity remain
those of S1973/S1975.
