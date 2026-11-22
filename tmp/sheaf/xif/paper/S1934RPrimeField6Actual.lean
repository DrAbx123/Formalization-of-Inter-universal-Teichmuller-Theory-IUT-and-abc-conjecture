/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1934

# S1934: field 6 at R' is unconditional --- `GaloisCategory (FiniteEtale R')^op`

## What this file does

S1848 reduced field 6 of the six-field geometric fibre functor at the closed point
`(0,0)` of `Spec R'` exactly to the residue-field reflection statement

  `S1848FReflectsIsoMaps`:
    for `f : A --> B` in `FiniteEtale R'`, if `F' (x)_{R'} f` is an isomorphism, then
    `f` is an isomorphism.

S1849 split that statement exactly into the injectivity half `S1849KernelVanishes` and
the trace-form / equal-rank surjectivity half `S1849SurjectiveOnInjective`, the latter
following from `S1849EqualRankInclusion`.

Two results now close both inputs:

* S1910 proves `S1849KernelVanishes` outright and proves
  `S1910FReflectsIsoMaps : S1849EqualRankInclusion -> S1848FReflectsIsoMaps`;
* S1912 proves `S1912_EqualRankInclusion : S1849EqualRankInclusion` by the
  trace-dual-retraction argument (no normal-domain integral closedness).

Hence, with no remaining hypothesis,

  `S1934FReflectsIsoMaps : S1848FReflectsIsoMaps`
  `S1934BCReflectsIsos : S1835BCReflectsIsos`                 (field 6 verbatim)
  `S1934SixFieldsMissing : S1835SixFieldsMissing`             (fields 4, 5, 6)
  `S1934FiberFunctor`                                          (six-field fibre functor)
  `S1934GaloisCategory : GaloisCategory (FiniteEtale R')^op`.

The assembly goes through S1855 (the six-field `PreGaloisCategory.FiberFunctor`) and
S1877 (the `GaloisCategory` construction); nothing in either file is changed or
weakened.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.
Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`, as
checked by the `#print axioms` audit at the end.  All mathematical inputs are the
proved theorems of S1910 and S1912; this file introduces no new hypothesis.
-/

import tmp.sheaf.xif.paper.S1910FiberPurityActual
import tmp.sheaf.xif.paper.S1912EqualRankTraceRetractionActual
import tmp.sheaf.xif.paper.S1877RPrimeGaloisActual

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false

namespace LeanFormal.IUT.XiFPaper.S1934RPrimeField6Actual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual
open LeanFormal.IUT.XiFPaper.S1877RPrimeGaloisActual
open LeanFormal.IUT.XiFPaper.S1910FiberPurityActual
open LeanFormal.IUT.XiFPaper.S1912EqualRankTraceRetractionActual

/-! ## 1. Field 6, unconditional -/

/-- **`S1848FReflectsIsoMaps` is unconditional.**  S1910 proves the S1848 target from
the equal-rank inclusion, and S1912 proves the equal-rank inclusion. -/
theorem S1934FReflectsIsoMaps : S1848FReflectsIsoMaps :=
  S1910FReflectsIsoMaps S1912_EqualRankInclusion

/-- **Field 6 is unconditional**: base change along `R' -> Omega`, in the opposite
direction, reflects isomorphisms of finite etale `R'`-algebras. -/
theorem S1934BCReflectsIsos : S1835BCReflectsIsos :=
  S1848BCReflectsIsos_of_fiber S1934FReflectsIsoMaps

/-- The injectivity half of the residue-fibre statement, unconditional (S1910). -/
theorem S1934KernelVanishes : S1849KernelVanishes :=
  S1910KernelVanishes

/-- The surjectivity half of the residue-fibre statement, now unconditional. -/
theorem S1934SurjectiveOnInjective : S1849SurjectiveOnInjective :=
  (S1849FReflectsIsoMaps_iff_split.mp S1934FReflectsIsoMaps).2

/-- S1835's three "missing" six-field conditions are now all theorems. -/
theorem S1934SixFieldsMissing : S1835SixFieldsMissing :=
  ⟨S1855BCPreservesEpis, S1855BCPreservesQuotients, S1934BCReflectsIsos⟩

/-- The exact six-field residual of S1855 (field 6 alone) is now empty. -/
theorem S1934SixFieldsResidual : S1855SixFieldsMissing :=
  S1934BCReflectsIsos

/-! ## 2. The unconditional six-field fibre functor -/

/-- The genuine six-field `PreGaloisCategory.FiberFunctor S1835Fiber` at the closed
geometric point `(0,0)` of `Spec R'`, with no hypothesis. -/
@[implicit_reducible]
noncomputable def S1934FiberFunctor :
    @PreGaloisCategory.FiberFunctor S1877Target S1779AlgR_category
      S1830Main.S1830PreGaloisCategory S1835Fiber :=
  S1877FiberFunctor S1934BCReflectsIsos

/-! ## 3. The Galois category -/

/-- **Main theorem: `GaloisCategory (FiniteEtale R')^op`, unconditionally.**

This is the target object: S1830 supplies the unconditional `PreGaloisCategory`,
S1855 supplies the six-field fibre functor, and S1934 has now discharged field 6. -/
theorem S1934GaloisCategory :
    GaloisCategory (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ :=
  S1877GaloisCategory_of_residue S1934FReflectsIsoMaps

/-- The same target, with the type written in S1779's notation `S1779AlgR` for
`(FiniteEtale R')^op`. -/
theorem S1934GaloisCategoryAlg : GaloisCategory S1779AlgR :=
  S1934GaloisCategory

/-- The same conclusion directly from field 6 in its verbatim S1835 form. -/
theorem S1934GaloisCategory_of_BC :
    GaloisCategory (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ :=
  S1877GaloisCategory S1934BCReflectsIsos

/-- The S1815 route to the quotient-colimit field, with field 6 unconditional. -/
theorem S1934GaloisCategoryOfS1815 :
    GaloisCategory (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ :=
  S1877GaloisCategoryOfS1815 S1934BCReflectsIsos

/-- The conclusion through S1779's algebra-side Galois data. -/
theorem S1934GaloisCategoryOfData :
    GaloisCategory (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ :=
  S1877GaloisCategoryOfData S1934BCReflectsIsos

/-! ## 4. Formal checks and axiom audit -/

#check S1934FReflectsIsoMaps
#check S1934BCReflectsIsos
#check S1934KernelVanishes
#check S1934SurjectiveOnInjective
#check S1934SixFieldsMissing
#check S1934SixFieldsResidual
#check S1934FiberFunctor
#check S1934GaloisCategory
#check S1934GaloisCategoryAlg
#check S1934GaloisCategory_of_BC
#check S1934GaloisCategoryOfS1815
#check S1934GaloisCategoryOfData

#print axioms S1934FReflectsIsoMaps
#print axioms S1934BCReflectsIsos
#print axioms S1934KernelVanishes
#print axioms S1934SurjectiveOnInjective
#print axioms S1934SixFieldsMissing
#print axioms S1934SixFieldsResidual
#print axioms S1934FiberFunctor
#print axioms S1934GaloisCategory
#print axioms S1934GaloisCategoryAlg
#print axioms S1934GaloisCategory_of_BC
#print axioms S1934GaloisCategoryOfS1815
#print axioms S1934GaloisCategoryOfData

end LeanFormal.IUT.XiFPaper.S1934RPrimeField6Actual
