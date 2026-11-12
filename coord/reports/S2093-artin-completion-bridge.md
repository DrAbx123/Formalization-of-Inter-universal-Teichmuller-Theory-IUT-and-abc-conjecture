# S2093: Artin retyped and M2a-core completion isomorphism

Date: 2026-11-02. Layer O; consumer S2027 M2a / S2024.

## Actual

Imports S2027, S2089 (maxAbelian equality + Galois equiv), and
Reciprocity.ProfiniteCompletion.

- artinRetyped :
    (localField p U)^x ->* Gal(maximalAbelianExtension p U / localField p U)
  = galoisGroupEquiv U . PadicField.artin.
- localReciprocityIsomorphism :
    unitProfiniteCompletion p U ≃* Gal(maximalAbelianExtension p U / localField p U)
  = artinCompletionEquiv (LANA) trans galoisGroupEquiv (S2089).

Lean:

  tmp/sheaf/xif/paper/S2093ArtinM2aBridge.lean
  source SHA256 909A4CA5959F99869116E8123C521040A96B7E0B473171E8039CDD3E8962192E
  EXIT=0
  olean SHA256 229F1CD3DEC0AC0C474FDCCD7592D5DBE0E1BCEACFDDA741D73F11D2753820E1
  size 244152

Axioms:

  artinRetyped                : propext, Classical.choice, Quot.sound
  localReciprocityIsomorphism : propext, Classical.choice, Quot.sound

## Exact first missing

S2027 LocalArtinSourceData.artin requires

  mu p U ≃* CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)).

The completion isomorphism above gives only

  unitProfiniteCompletion p U ≃* Gal(L^ab/L),

not its restriction to torsion.  The exact missing object is M2a-torsion:

  TorsionCompletionIso U :
    Nonempty (CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U)

equivalently the local CFT theorem that torsion of L^x-hat is mu(L).
Note unitProfiniteCompletion has no CommGroup instance in the tree;
a torsion statement must be stated with an explicit torsion subgroup or
a commutativity instance, otherwise CommGroup.torsion does not elaborate.

Once this is supplied, composing with torsionMulEquiv of
localReciprocityIsomorphism and galoisGroupMaximalAbelian gives
S2027's artin field, and with the M2c carrier the LocalArtinSourceData.

## M2b

Brauer.ArtinTransfer is not copied/ported yet; M2b remains after Brauer closure.

## Conclusion

- BUILT: artinRetyped and localReciprocityIsomorphism, EXIT=0, axioms trio.
- MISSING: M2a-torsion (torsion completion ≃ mu).
- no fake; no LocalArtinSourceData inhabitant assumed.
