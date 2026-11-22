# S1970: H-comparison naturality and the exact first missing (attempt)

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1970IsoCommaStackActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1970IsoCommaStackActual.olean
Exit: 0 (lake env lean -j1 -R D:\lean -o <olean> <source>), no errors, no warnings.

## Verification

- Build: EXIT=0, no errors, no warnings.
- Import re-check: EXIT=0 (scratch module importing the olean and #checking the
  main declarations; the scratch module was removed afterwards).
- Source scan: no actual sorry/admit/axiom declaration; the only occurrence of
  the word sorry is in the honesty paragraph.
- Axiom audit (#print axioms): only propext, Classical.choice, Quot.sound for
  every declaration in the file.
- SHA256 source: 46531C494FB38DB41D11D89DD4AD348C383F2EF4129F1E6E4B3C0FB749521FBE
- SHA256 olean: A19801251133BE6E449AE01E84CBD466639BFC91D4417F2BE8E10798C01D3F62

## What is proved

1. The exact decomposition of the target: S1970IsoCommaStack f g is equivalent
   to the prestack half and the effectivity half
   (S1970IsoCommaStack_iff_prestack_effectivity), transported from S1956.

2. The exact first missing statement (A) is named as
   S1970HComparisonNaturalityAll (= S1956HComparisonNaturalityAll), and the
   second missing statement (B) is named as S1970EffectivityAll. No inhabitant
   of either is asserted.

3. The first genuinely new consumer of (A): if the componentwise naturality of
   the first (resp. second) H-comparison holds, its components assemble into a
   natural transformation of hom presheaves
     A.fiber.presheafHom M.left N.left --> C.fiber.presheafHom (f_S M.left) (f_S N.left)
   (resp. the B-side one). This is S1970FstToHNatTrans / S1970SndToHNatTrans,
   and S1970HComparisonNaturalityAll_gives_natTrans for the uniform form.

## Exact first missing

(A) S1970HComparisonNaturalityAll / S1956HComparisonNaturalityAll:
the componentwise naturality of the two H-comparison maps with respect to the
pullHom restriction maps of the presheaves of morphisms.

The proof attempt reduced the componentwise identity to three ingredients that
are already present in the tree:
  * natCompInvApp_comp (S1935) for the f-side inverse comparison at the source,
  * NatTrans.naturality of Cat.Hom.toNatIso (g.map.naturality ...) at the
    morphism between the restricted homs,
  * natCompHomApp_comp (S1935) for the f-side comparison at the target.
The abstract assembly of these three identities was carried out on paper and
driven through Lean up to the final associativity/cancellation steps.  The
remaining obstruction, as observed in this session, is formal: composing the
Cat.Hom.toNatIso comparisons with the pullHom restrictions produces types
whose object components are only related through Cat.Hom.comp_obj /
Functor.map_comp, and the final componentwise associativity rewrites did not
elaborate.  No mathematical input beyond the three displayed ingredients was
identified as missing, but the assembly is not claimed as proved.

(B) S1970EffectivityAll / S1956IsoCommaEffectivity remains untouched: it is the
essential surjectivity of toDescentData for every covering sieve, i.e. the
object-level 2-limit interchange for a triple of descent data.

## Honest boundary

No fake IsStack, no sorry, no axiom, no Shrink/ULift/PUnit, no change of the
target.  Neither (A) nor (B) is inhabited.  The pullback-of-sheaves step from
(A) to IsPrestack is not formalized.  The file therefore reports the exact
first missing, as required by the fallback of the task.