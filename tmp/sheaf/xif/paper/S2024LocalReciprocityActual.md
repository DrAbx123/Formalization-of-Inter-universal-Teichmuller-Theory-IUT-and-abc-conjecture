# S2024: (M2) local reciprocity on torsion -- reduction and exact first missing

Date: 2026-11-01.  File: tmp/sheaf/xif/paper/S2024LocalReciprocityActual.lean.
Consumer: tmp/sheaf/xif/paper/_S2024Consumer.lean.
Upstream: tmp/sheaf/xif/paper/S2017VerlagerungActual.lean (M1 infrastructure:
transferAb, verlagerungOpen, toStage, muQZ, muHatZ, muQZComparison,
muHatComparison).

## Outcome

(M2) is **not proved**.  Its construction needs local class field theory for
finite extensions of Q_p (the local Artin/reciprocity map), which is absent
from Mathlib v4.32.2 and from this tree.  The package instead:

1. isolates the exact missing datum as the structure LocalReciprocityData p
   (levelwise torsion reciprocity + the Verlagerung compatibility square);
2. proves that this datum yields S2017's two comparison propositions
   muQZComparison p and muHatComparison p, hence that (M2) is precisely the
   remaining input of the S2017 chain;
3. proves, unconditionally, that every element of the direct limit muQZ p is
   represented in a single stage (muQZ_exists_stage), the ingredient needed to
   pass from levelwise information to the limit;
4. records the abstract-vs-profinite abelianization caveat (M2c) without
   hiding it.

No sorry, admit, axiom, True/PUnit slot, empty structure, arbitrary
inhabitant, or assumption-only Nonempty gate is introduced.

## Constructed / proved (EXIT = 0)

* torsionUnitsMap_comp, torsionUnitsMap_injective: functoriality and
  injectivity of the torsion-unit map of a ring hom.
* additiveOfMulHom and additiveOfMulHom_injective: passage from a
  multiplicative hom to an additive hom through Additive.
* fixedField_le, fixedFieldTorsionUnitsInclusion and its injectivity:
  for H <= K the fixed-field inclusion L_K <= L_H induces
  torsion(L_K)^x -> torsion(L_H)^x.
* torsionUnitsMap_val_comp_inclusion: the induced torsion-unit map is
  compatible with the ambient embedding into the algebraic closure.
* LocalReciprocityData p, with fields equiv and transfer_compat: the formal
  (M2) datum on the tree's carriers.
* stageHom, stageHom_apply, stageHom_toStage, stageHom_injective: the
  levelwise maps to the torsion of the algebraic closure and their transfer
  compatibility and injectivity.
* toStage_injective_of_data: under (M2), the Verlagerung on torsion is
  injective (it is the inclusion of roots of unity).
* muQZ_exists_stage: unconditional single-stage representation in the
  colimit (uses only downward directedness of the open-subgroup lattice).
* muQZToClosure, muQZToClosure_of, muQZToClosure_injective,
  muQZToClosure_surjective, muQZAddEquiv: the assembled comparison
  muQZ p ~= torsion(O^tri)^x from a local reciprocity datum.
* muQZComparison_of_data: LocalReciprocityData p -> muQZComparison p.
* kummerCyclotomeCongr, multiplicativeAdditiveMulEquiv,
  muHatComparison_of_muQZComparison, muHatComparison_of_data:
  muQZComparison p -> muHatComparison p.
* muQZ_addEquiv_addCircle_of_data: under (M2), muQZ p ~= Q/Z, i.e. the
  source's mu_{Q/Z}(G_v) is literally the rational circle.
* muQZComparison_iff_rationalCircle: unconditionally, muQZComparison p is
  equivalent to Nonempty (muQZ p ~= AddCircle 1), i.e. its content is exactly
  "the group-theoretic cyclotome is Q/Z".
* localReciprocityOnTorsion_of_data: the S2011 statement follows from the
  datum.
* localReciprocityDataMissing, localReciprocityOnTorsionMissing,
  localReciprocityLevelwiseMissing, levelwiseLocalReciprocity: the missing
  propositions, stated and not proved.
* localReciprocityLevelwiseMissing_of_dataMissing,
  muQZComparison_of_dataMissing, muHatComparison_of_dataMissing: the
  consequences of the missing datum, so that a future construction plugs in
  without changing the interfaces.

## Exact first missing, in dependency order

(M2a) Levelwise local reciprocity on torsion: for every open U,
      torsion (Ab U) ~= torsion (FixedField U)^x.  This is the local Artin
      map on torsion for the finite extension FixedField U / Q_p.
      Missing: no reciprocity map, no maximal abelian extension L^ab as an
      intermediate field, and no identification Gal(L^ab/L) ~= hat(L^x) in
      Mathlib or in the tree.  Generic norm maps and profinite completions of
      abstract groups do exist; the reciprocity map and its norm
      compatibility do not.  This is the first genuinely missing input.

(M2b) Transfer compatibility: for H <= K, under the levelwise
      identifications, verlagerungOpen h must correspond to the inclusion
      torsion(FixedField K)^x -> torsion(FixedField H)^x.  In local class
      field theory this is the norm-compatibility of the reciprocity map
      (Ver o rec_K = rec_L o incl for L <= K).  The present file isolates it
      as the field transfer_compat of LocalReciprocityData and proves that
      exactly this field is what the universal property of muQZ consumes.

(M2c) Abstract vs. profinite abelianization: Mathlib's Abelianization U is
      the quotient by the ordinary commutator subgroup, while the source's
      (U^ab) is the profinite (closed-commutator) abelianization.  Local CFT
      identifies the profinite abelianization with hat(L^x), whose torsion is
      mu(L).  localReciprocityOnTorsion p is stated on the abstract carrier;
      its identification with the literal profinite source statement
      requires an extra comparison between the abstract and profinite
      torsion.  That comparison is not supplied by the tree's definitions and
      is not proved here.  The reduction below is a correct theorem about the
      same abstract carrier as S2011; the literal source statement
      additionally needs (M2c).

## Evidence

* source: tmp/sheaf/xif/paper/S2024LocalReciprocityActual.lean, 557 lines,
  SHA256 35491F871552315FC64B674608FD359423C2EDDA171528B5FCC3C68A00222D07.
* compile: lake env lean -R D:/lean -s 65536 -M 8192
  -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2024LocalReciprocityActual.olean
  tmp/sheaf/xif/paper/S2024LocalReciprocityActual.lean
  EXIT = 0, 0 errors, 0 warnings.
* olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S2024LocalReciprocityActual.olean,
  1,086,368 bytes, SHA256
  68DBEF359B0DB1E793B6AA617DBD3D71AC4D8A9C0F0BD3B25A1D45BC8125366B.
* axiom probes (#print axioms in the file): all listed declarations depend
  only on propext, Classical.choice, Quot.sound.
* consumer: tmp/sheaf/xif/paper/_S2024Consumer.lean, EXIT = 0; it re-checks
  the main theorem types and the axiom sets.  Source SHA256
  72BCB31C010A70807DB1D2A1FA868C53002FB2EFA9237F95574972A10171885E, olean
  SHA256 D8E4A7330EFCAF7E17C3ABFC62369116259F088C351BB70A79A607CBD864034F.
* logs: tmp/sheaf/xif/paper/S2024Compile.log,
  tmp/sheaf/xif/paper/_S2024Consumer.log.

## Not run

Full Project build, target comparator, independent review, and the [AbsTopIII]
group-theoretic construction itself.

## Next executable step

Construct (M2a) at one finite level: the local Artin map for a finite
extension L/Q_p expressed as a map (L^× -> Gal(L^ab/L)) with dense image,
together with the identification on torsion with mu(L); then (M2b) follows
from the norm-compatibility of the Artin map.  Both require new definitions
(maximal abelian extension, reciprocity map) that do not exist in the tree
yet, so they are the next definitions to build, not merely lemmas to prove.
