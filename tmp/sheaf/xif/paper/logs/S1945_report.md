# S1945: the actual iso-comma site pseudofunctor data -- S1864 (a) closed

Date: 2026-11-01.
Source: tmp/sheaf/xif/paper/S1945SitePseudofunctorDataActual.lean
Olean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1945SitePseudofunctorDataActual.olean

## Verification

- Build command:
  lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1945SitePseudofunctorDataActual.olean tmp/sheaf/xif/paper/S1945SitePseudofunctorDataActual.lean
- EXIT=0, 0 errors, 0 warnings.
- Source: 32462 bytes, 633 lines,
  SHA256 42A5DDEFCFAD91A6585CC891A4928AF4FB89A56303A8E41F261FDE2C16E710E9.
- Olean: 671112 bytes,
  SHA256 9A7453A554F52E14B445BBC47625A6F76D4B5D787F39DA96627B74D8E792FF54.
- Import re-check: EXIT=0 (a scratch module imports the built olean and #checks the
  main declarations; it reports the expected types).
- Axiom audit (#print axioms on all main declarations): only
  [propext, Classical.choice, Quot.sound].  No sorryAx, no axiom declaration,
  no placeholder, no fake coherence.
- Source scan: no 'sorry', 'admit', or axiom declaration.

## What is proved unconditionally

1. siteCompGHom: the hom-direction g-side pasting identity
   (g.map W).map (B.mapComp phi psi).hom ; (g.nat psi).hom ;
   (C.map psi).map (g.nat phi).hom
     = (g.nat (phi ; psi)).hom ; (C.mapComp phi psi).hom,
   proved from S1935's natCompHomApp_comp (naturality_comp_hom with the trailing
   inverse comparison cancelled).

2. Direction analysis settled.  S1864SiteComparisonRight g phi is
   (Cat.Hom.toNatIso (g.map.naturality phi)).symm, so its .hom is
   (g.map.naturality phi).inv.  Therefore S1890CompSquare consumes the
   inverse-naturality direction, which is exactly S1890SiteCompG.  The composite
   square is proved from S1890SiteCompF, S1890SiteCompC and S1890SiteCompG
   (siteCompSquare); the hom-direction identity is not needed for it, but is
   supplied as requested.

3. siteIdC: the C-side mapId naturality at a site morphism.
   siteIdSquare: S1890IdSquare for the site data, from S1890SiteIdF, siteIdC and
   S1890SiteIdG.

4. siteMapComp: the concrete comparison from S1890RestrictCompIso applied to the
   site data; siteMapId: from S1890RestrictIdIso.  Component computations:
   siteMapComp_fst/snd/inv_fst/inv_snd, siteMapId_fst/snd, isoCommaMap_fst_map/
   snd_map, obj_left/right_isoCommaMap, siteAssociator_fst/snd,
   siteLeftUnitor_fst/snd, siteRightUnitor_fst/snd (all rfl).

5. The three coherence equations:
   siteCoherence_assoc, siteCoherence_leftUnitor, siteCoherence_rightUnitor,
   proved by reduction along S1836IsoComma_hom_ext to
   A.source.fiber.map2_associator / map2_left_unitor / map2_right_unitor and
   B.source.fiber's, with the eqToHom (by simp) right-hand side identified with
   the map2 of the locally discrete associator/unitor via
   Bicategory.Strict.associator_eqToIso, left/rightUnitor_eqToIso and
   PrelaxFunctor.map2_eqToHom.

6. sitePseudofunctor: a genuine pseudofunctor
   LocallyDiscrete (SchemeOverField S1726K)^op !--> Cat, built with
   pseudofunctorOfIsLocallyDiscrete, with
   obj U = S1890IsoCommaObj f g U and map phi = S1890IsoCommaMap f g phi
   definitionally (sitePseudofunctor_obj/map/mapComp/mapId).

7. S1945SitePseudofunctorCoherence:
   S1890PseudofunctorCoherence f g (fun phi psi => siteMapComp f g phi psi)
   (fun U => siteMapId f g), for all A B C f g.

8. S1935RemainingSitePseudofunctor_holds:
   S1935RemainingSitePseudofunctor f g, for all A B C f g.  This closes the exact
   remaining obligation of S1935 and hence S1864 (a).

9. S1864PartA: the (a)-form statement -- the canonical pseudofunctor has the
   required iso-comma values and the required site-restriction 1-cells,
   definitionally.

## Exact state of S1864 after this file

S1864 (a) (the category-valued pseudofunctor with iso-comma fibres on the whole
etale site, with its comparison data and coherence) is CLOSED for every cospan of
actual finite-etale cover maps.

Remaining and untouched here:
- (b) IsStack (effective descent for the iso-comma pseudofunctor);
- (c) the representably finite-etale structure map to the orbicurve stack;
- (d) the bicategorical universal property / realization comparison.

None of (b), (c), (d) is claimed or assumed.  The next concrete missing item of
the S1864 decomposition is (b) IsStack.

## Notes

- The proof does not use Pseudofunctor.mkOfOplax/mkOfLax or any lifting of the
  comparison data through a lax functor; the three coherence laws are proved
  directly from the two stack pseudofunctors' coherence.
- The only structural input from S1890 is S1890RestrictCompIso /
  S1890RestrictIdIso, used exactly as intended.
- No new assumptions, no sorries, no axioms, no fake or vacuous coherence.
