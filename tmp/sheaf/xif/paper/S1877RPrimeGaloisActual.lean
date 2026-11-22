/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1877
-/

import tmp.sheaf.xif.paper.S1855RPrimeFiberIntegrationActual
import tmp.sheaf.xif.paper.S1815AffineQuotientColimitsActual
import tmp.sheaf.xif.paper.S1849RPrimeReflectCompleteActual

/-!
# S1877: the Galois category of finite etale R'-algebras, conditional on field 6

## Context

S1855 assembles the genuine six-field fibre functor
`S1835Fiber = CommAlgCat.FiniteEtale.fiber R' Omega` at the closed geometric
point `(0,0)` from:

* S1830's unconditional `PreGaloisCategory (FiniteEtale R')^op`;
* S1846's field 4 and S1851's field 5;
* one explicit hypothesis, field 6 `S1835BCReflectsIsos`.

S1815 independently proves the algebra-side quotient-colimit (G2) field
for the same category (its `General.hasColimitsOfShape_finiteEtaleAlg`,
Section 1), and also transports it to the affine finite-etale slice; only the
algebra-side theorem is used here.  S1830 proves (G3).
S1848/S1849 identify field 6 exactly with the residue-field statement
`S1848FReflectsIsoMaps` and with the conjunction
`S1849KernelVanishes ∧ S1849SurjectiveOnInjective`.

## What this file does

It performs the final assembly of the algebra-side `GaloisCategory`:

* `S1877AlgGaloisData`: the S1779 algebra-side Galois data, with S1830's
  unconditional pre-Galois structure and S1855's conditional fibre functor;
* `S1877GaloisCategory`: `GaloisCategory (FiniteEtale R')^op` from field 6;
* `S1877GaloisCategoryOfS1815`: the same conclusion using S1815's
  quotient-colimit proof (G2) together with S1830's (G3), rather than S1830's
  packaged pre-Galois structure;
* `S1877GaloisCategory_of_residue` and `S1877GaloisCategory_of_split`:
  the same conclusion from the exact field-6 interfaces of S1848/S1849;
* `S1877Field6_iff_*`: field 6 is exactly these interfaces, not a new
  hypothesis.

## What is still missing

Field 6 is still not proved in this checkout.  In the S1849 route the
remaining inputs are `S1849KernelVanishes`, the closed-fibre rank equality
(step (ii)), and the trace-form/equal-rank inclusion
`S1849EqualRankInclusion`; S1849's `S1848FReflectsIsoMaps_of_route` proves
field 6 from exactly those three inputs.  S1860 attacks the trace-duality
part, but trace duality alone is not field 6: the kernel-vanishing, rank
equality and integral-descent/equal-rank inputs are separate.  Nothing from
S1860 is assumed or imported here, and this file does not claim that S1860
closes field 6.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in
this file.  Every declaration depends only on `propext`,
`Classical.choice` and `Quot.sound`.  The main theorem is explicitly
conditional on field 6; it is not an unconditional construction.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1877RPrimeGaloisActual

open CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual

/-! ## 1. The S1830 pre-Galois structure and the S1855 fibre functor -/

/-- The exact target category: the opposite of finite etale `R'`-algebras. -/
abbrev S1877Target : Type 1 := (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ

/-- S1830's unconditional `PreGaloisCategory` on the target. -/
theorem S1877PreGaloisCategory : PreGaloisCategory S1877Target :=
  S1830Main.S1830PreGaloisCategory

/-- The six-field fibre functor of S1855, with its instance argument fixed to
S1830's pre-Galois structure. -/
@[implicit_reducible]
noncomputable def S1877FiberFunctor (hIso : S1835BCReflectsIsos) :
    @PreGaloisCategory.FiberFunctor S1877Target S1779AlgR_category
      S1830Main.S1830PreGaloisCategory S1835Fiber :=
  S1855FiberFunctor hIso

/-- The algebra-side Galois data of S1779: S1830's unconditional
pre-Galois structure, the actual geometric fibre functor, and S1855's
six-field structure conditional on field 6. -/
@[implicit_reducible]
noncomputable def S1877AlgGaloisData (hIso : S1835BCReflectsIsos) :
    S1779AlgGaloisData where
  preGalois := S1830Main.S1830PreGaloisCategory
  fiber := S1835Fiber
  fiberFunctor := S1877FiberFunctor hIso

/-! ## 2. The Galois category, conditional on field 6 -/

/-- **S1877: `GaloisCategory (FiniteEtale R')^op`, conditional on field 6.**

This is the actual target: S1830 supplies the unconditional
`PreGaloisCategory`, S1855 supplies the genuine geometric fibre functor with
fields 1--5 proved and field 6 as the only hypothesis. -/
theorem S1877GaloisCategory (hIso : S1835BCReflectsIsos) :
    GaloisCategory S1877Target := by
  letI : PreGaloisCategory S1877Target := S1830Main.S1830PreGaloisCategory
  exact GaloisCategory.mk ⟨S1835Fiber, ⟨S1877FiberFunctor hIso⟩⟩

/-- The same Galois-category conclusion through the S1779 algebra-side data. -/
theorem S1877GaloisCategoryOfData (hIso : S1835BCReflectsIsos) :
    GaloisCategory S1877Target := by
  let D := S1877AlgGaloisData hIso
  letI : PreGaloisCategory S1877Target := D.preGalois
  exact GaloisCategory.mk ⟨D.fiber, ⟨D.fiberFunctor⟩⟩

/-! ## 3. The S1815 route to the quotient-colimit field -/

/-- S1815's quotient-colimit theorem, in the exact form of S1779's (G2). -/
theorem S1877QuotientsViaS1815 : S1779QuotientsMissing := by
  intro G _ _
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  exact LeanFormal.IUT.XiFPaper.S1815AffineQuotientColimitsActual.General.hasColimitsOfShape_finiteEtaleAlg
    (R := S1779R) (G := G)

/-- The pre-Galois structure assembled from S1815's (G2) and S1830's (G3). -/
@[implicit_reducible]
noncomputable def S1877PreGaloisCategoryOfS1815 : PreGaloisCategory S1877Target :=
  S1779PreGaloisCategory S1877QuotientsViaS1815 S1830Main.S1830MonoMissing

/-- The S1855 fibre functor, with the S1815-based pre-Galois instance. -/
@[implicit_reducible]
noncomputable def S1877FiberFunctorOfS1815 (hIso : S1835BCReflectsIsos) :
    @PreGaloisCategory.FiberFunctor S1877Target S1779AlgR_category
      S1877PreGaloisCategoryOfS1815 S1835Fiber :=
  @S1835FiberFunctorOf S1855BCPreservesEpis S1855BCPreservesQuotients hIso
    S1877PreGaloisCategoryOfS1815

/-- The S1779 algebra-side Galois data using S1815's quotient-colimit proof. -/
@[implicit_reducible]
noncomputable def S1877AlgGaloisDataOfS1815 (hIso : S1835BCReflectsIsos) :
    S1779AlgGaloisData where
  preGalois := S1877PreGaloisCategoryOfS1815
  fiber := S1835Fiber
  fiberFunctor := S1877FiberFunctorOfS1815 hIso

/-- **The S1815 route to `GaloisCategory (FiniteEtale R')^op`**, conditional
on field 6.  It uses S1815 for (G2), S1830 for (G3), and S1855 for the
fibre functor. -/
theorem S1877GaloisCategoryOfS1815 (hIso : S1835BCReflectsIsos) :
    GaloisCategory S1877Target := by
  letI : PreGaloisCategory S1877Target := S1877PreGaloisCategoryOfS1815
  exact GaloisCategory.mk ⟨S1835Fiber, ⟨S1877FiberFunctorOfS1815 hIso⟩⟩

/-! ## 4. The exact field-6 interfaces -/

/-- Field 6 is exactly its element-free concrete form. -/
theorem S1877Field6_iff_concrete :
    S1835BCReflectsIsos ↔ S1835BCReflectsIsosConcrete :=
  S1835BCReflectsIsos_iff_concrete

/-- Field 6 is exactly the residue-field reflection statement of S1848. -/
theorem S1877Field6_iff_residue :
    S1835BCReflectsIsos ↔ S1848FReflectsIsoMaps :=
  S1848BCReflectsIsos_iff

/-- Field 6 is exactly the S1849 splitting into kernel vanishing and
surjectivity on injective maps. -/
theorem S1877Field6_iff_split :
    S1835BCReflectsIsos ↔
      S1849KernelVanishes ∧ S1849SurjectiveOnInjective :=
  S1848BCReflectsIsos_iff.trans S1849FReflectsIsoMaps_iff_split

/-- The Galois-category conclusion from S1848's residue-field form of field 6. -/
theorem S1877GaloisCategory_of_residue (h : S1848FReflectsIsoMaps) :
    GaloisCategory S1877Target :=
  S1877GaloisCategory (S1848BCReflectsIsos_of_fiber h)

/-- The Galois-category conclusion from S1849's exact splitting of field 6. -/
theorem S1877GaloisCategory_of_split
    (h : S1849KernelVanishes ∧ S1849SurjectiveOnInjective) :
    GaloisCategory S1877Target :=
  S1877GaloisCategory_of_residue (S1849FReflectsIsoMaps_iff_split.mpr h)

/-- The Galois-category conclusion from the three inputs of S1849's route:
kernel vanishing, the closed-fibre rank equality, and equal-rank inclusion. -/
theorem S1877GaloisCategory_of_route
    (hker : S1849KernelVanishes)
    (hii : ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
      IsIso ((S1848BCF).map f) →
      ∀ (p : PrimeSpectrum S1779R),
        Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p)
    (hiii : S1849EqualRankInclusion) :
    GaloisCategory S1877Target :=
  S1877GaloisCategory_of_residue (S1848FReflectsIsoMaps_of_route hker hii hiii)

/-! ## 5. Checks and axiom audit -/

#check S1877Target
#check S1877PreGaloisCategory
#check S1877FiberFunctor
#check S1877AlgGaloisData
#check S1877GaloisCategory
#check S1877GaloisCategoryOfData
#check S1877QuotientsViaS1815
#check S1877PreGaloisCategoryOfS1815
#check S1877FiberFunctorOfS1815
#check S1877AlgGaloisDataOfS1815
#check S1877GaloisCategoryOfS1815
#check S1877Field6_iff_concrete
#check S1877Field6_iff_residue
#check S1877Field6_iff_split
#check S1877GaloisCategory_of_residue
#check S1877GaloisCategory_of_split
#check S1877GaloisCategory_of_route

#print axioms S1877PreGaloisCategory
#print axioms S1877FiberFunctor
#print axioms S1877AlgGaloisData
#print axioms S1877GaloisCategory
#print axioms S1877GaloisCategoryOfData
#print axioms S1877QuotientsViaS1815
#print axioms S1877PreGaloisCategoryOfS1815
#print axioms S1877FiberFunctorOfS1815
#print axioms S1877AlgGaloisDataOfS1815
#print axioms S1877GaloisCategoryOfS1815
#print axioms S1877Field6_iff_concrete
#print axioms S1877Field6_iff_residue
#print axioms S1877Field6_iff_split
#print axioms S1877GaloisCategory_of_residue
#print axioms S1877GaloisCategory_of_split
#print axioms S1877GaloisCategory_of_route

end LeanFormal.IUT.XiFPaper.S1877RPrimeGaloisActual
