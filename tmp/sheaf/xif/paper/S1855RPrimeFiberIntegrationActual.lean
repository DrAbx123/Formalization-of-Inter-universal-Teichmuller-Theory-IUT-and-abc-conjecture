/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1855
-/

import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import tmp.sheaf.xif.paper.S1846MonoFFActual
import tmp.sheaf.xif.paper.S1851RPrimeQuotientsCompleteActual
import tmp.sheaf.xif.paper.S1848RPrimeReflectActual

/-!
# S1855: the six-field fibre functor at R' with only field 6 left open

S1835 stated the six-field `PreGaloisCategory.FiberFunctor S1835Fiber` at the closed
geometric point `(0,0)` of `Spec R'` as an assembly of three unconditional fields
(terminal objects, pullbacks, finite coproducts) and three exact base-change conditions
`S1835SixFieldsMissing = S1835BCPreservesEpis ∧ S1835BCPreservesQuotients ∧
S1835BCReflectsIsos`.  Fields 4 and 5 have since been proved:

* field 4 (`S1835BCPreservesEpis`): `S1846BCPreservesEpis` (S1846, from the
  faithful flatness of a mono of finite etale `R'`-algebras);
* field 5 (`S1835BCPreservesQuotients`): `S1835BCPreservesQuotients_actual` (S1851,
  from finite-group fixed points commuting with the base change `R' -> Omega`).

This file performs the integration: it builds the genuine six-field
`PreGaloisCategory.FiberFunctor S1835Fiber` from S1835's fields 1--3, S1846's field 4,
S1851's field 5, and a single explicit hypothesis for field 6.  No hypothesis, axiom or
weakening is introduced anywhere else.

## What is in this file

* `S1855BCPreservesEpis`, `S1855BCPreservesQuotients`: the two now-actual base-change
  conditions, quoted from S1846 and S1851;
* `S1855PreservesEpis`, `S1855PreservesQuotients`: the corresponding fields for the
  actual fibre functor, through S1835's reductions;
* `S1855FiberFunctor (hIso : S1835BCReflectsIsos) : PreGaloisCategory.FiberFunctor
  S1835Fiber`: the six-field structure with fields 1--5 actual and field 6 the only
  hypothesis;
* `S1855FiberFunctorOfConcrete`: the same from S1835's element-free concrete form
  `S1835BCReflectsIsosConcrete`;
* `S1855FiberFunctorOfResidue`: the same from S1848's exact residue-field form
  `S1848FReflectsIsoMaps`, the interface for the S1849/S1853 trace-form route;
* `S1855SixFieldsMissing` and `S1855SixFieldsMissing_iff`: the remaining content of
  `S1835SixFieldsMissing` is *exactly* field 6, `S1835BCReflectsIsos`.

## What is still missing

Field 6 only: `S1835BCReflectsIsos : (S1835BC).op.ReflectsIsomorphisms`, equivalently
`S1835BCReflectsIsosConcrete`.  S1848 reduces it further, exactly, to the residue-field
statement `S1848FReflectsIsoMaps`; S1849 proves the exact splitting of that statement
into `S1849KernelVanishes` and `S1849SurjectiveOnInjective`, the latter being the
trace-form / equal-rank statement (`S1849EqualRankInclusion`) under attack in S1853.
S1849's route theorem `S1848FReflectsIsoMaps_of_route` additionally takes the
closed-fibre rank equality (step (ii)) as an explicit hypothesis, so at the S1849
frontier the open inputs are `S1849KernelVanishes`, the rank equality, and the
trace-form `S1849EqualRankInclusion`.  Nothing of that route is assumed here: this file
only exposes the exact field-6 hypothesis that any such result must discharge.

## Verification (session S1855, 2026-11-01)

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1855RPrimeFiberIntegrationActual.olean
      tmp/sheaf/xif/paper/S1855RPrimeFiberIntegrationActual.lean

-> EXIT=0, no errors, no warnings, no `sorryAx`; every `#print axioms` below prints
only `[propext, Classical.choice, Quot.sound]`.  The compiled olean is
`.lake/build/lib/lean/tmp/sheaf/xif/paper/S1855RPrimeFiberIntegrationActual.olean`.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.
Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms` below).  `S1855FiberFunctor` has field 6 as an explicit hypothesis and
is *not* an unconditional construction; nothing in this file claims that field 6 is
proved.  The `PreGaloisCategory` instance used is S1830's unconditional theorem
`S1830Main.S1830PreGaloisCategory`, registered locally.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual

open CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1846MonoFFActual
open LeanFormal.IUT.XiFPaper.S1851RPrimeQuotientsCompleteActual
open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual

attribute [local instance] S1779PointClosureAlgebra
attribute [local instance] S1830Main.S1830PreGaloisCategory

/-! ## 1. Fields 4 and 5, now actual -/

/-- Field 4 at the base-change level, discharged by S1846. -/
theorem S1855BCPreservesEpis : S1835BCPreservesEpis :=
  S1846BCPreservesEpis

/-- Field 5 at the base-change level, discharged by S1851. -/
theorem S1855BCPreservesQuotients : S1835BCPreservesQuotients :=
  S1835BCPreservesQuotients_actual

/-- Field 4 for the actual geometric fibre functor. -/
theorem S1855PreservesEpis : Functor.PreservesEpimorphisms S1835Fiber :=
  S1835PreservesEpis_of S1855BCPreservesEpis

/-- Field 5 for the actual geometric fibre functor. -/
theorem S1855PreservesQuotients :
    ∀ (G : Type) [Group G] [Finite G],
      PreservesColimitsOfShape (SingleObj G) S1835Fiber :=
  S1835PreservesQuotients_of S1855BCPreservesQuotients

/-! ## 2. The six-field fibre functor with only field 6 open -/

/-- **The six-field `PreGaloisCategory.FiberFunctor S1835Fiber`**, with fields 1--3 from
S1835, field 4 from S1846, field 5 from S1851, and field 6 as the only hypothesis. -/
@[implicit_reducible]
noncomputable def S1855FiberFunctor (hIso : S1835BCReflectsIsos) :
    PreGaloisCategory.FiberFunctor S1835Fiber :=
  S1835FiberFunctorOf S1855BCPreservesEpis S1855BCPreservesQuotients hIso

/-- The same construction from the concrete, element-free form of field 6 recorded in
S1835 (equivalent to `S1835BCReflectsIsos` by `S1835BCReflectsIsos_iff_concrete`). -/
@[implicit_reducible]
noncomputable def S1855FiberFunctorOfConcrete (h : S1835BCReflectsIsosConcrete) :
    PreGaloisCategory.FiberFunctor S1835Fiber :=
  S1855FiberFunctor (S1835BCReflectsIsos_iff_concrete.mpr h)

/-- The same construction from S1848's exact residue-field form of field 6,
`S1848FReflectsIsoMaps` (equivalent to `S1835BCReflectsIsos` by
`S1848BCReflectsIsos_iff`).  This is the interface through which the S1849/S1853
trace-form route plugs into the six-field structure: S1849 splits
`S1848FReflectsIsoMaps` into `S1849KernelVanishes` and `S1849SurjectiveOnInjective`,
the latter being the trace-form / equal-rank statement. -/
@[implicit_reducible]
noncomputable def S1855FiberFunctorOfResidue (h : S1848FReflectsIsoMaps) :
    PreGaloisCategory.FiberFunctor S1835Fiber :=
  S1855FiberFunctor (S1848BCReflectsIsos_of_fiber h)

/-! ## 3. What is left of `S1835SixFieldsMissing`: exactly field 6 -/

/-- The remaining content of S1835's six-field input, after S1846 and S1851: field 6. -/
def S1855SixFieldsMissing : Prop := S1835BCReflectsIsos

/-- **S1835's six-field residual is now exactly field 6.**  `S1835SixFieldsMissing`
(fields 4, 5, 6) is equivalent to `S1835BCReflectsIsos` (field 6 alone), because fields
4 and 5 are the proved theorems `S1846BCPreservesEpis` and
`S1835BCPreservesQuotients_actual`. -/
theorem S1855SixFieldsMissing_iff :
    S1835SixFieldsMissing ↔ S1855SixFieldsMissing :=
  ⟨fun h => h.2.2,
   fun h => ⟨S1855BCPreservesEpis, S1855BCPreservesQuotients, h⟩⟩

/-- The residual stated with field 6 verbatim. -/
theorem S1855SixFieldsMissing_iff_field6 :
    S1835SixFieldsMissing ↔ S1835BCReflectsIsos :=
  S1855SixFieldsMissing_iff

/-! ## 4. Checks and axiom audit -/

#check S1855BCPreservesEpis
#check S1855BCPreservesQuotients
#check S1855PreservesEpis
#check S1855PreservesQuotients
#check S1855FiberFunctor
#check S1855FiberFunctorOfConcrete
#check S1855FiberFunctorOfResidue
#check S1855SixFieldsMissing
#check S1855SixFieldsMissing_iff
#check S1855SixFieldsMissing_iff_field6

#print axioms S1855BCPreservesEpis
#print axioms S1855BCPreservesQuotients
#print axioms S1855PreservesEpis
#print axioms S1855PreservesQuotients
#print axioms S1855FiberFunctor
#print axioms S1855FiberFunctorOfConcrete
#print axioms S1855FiberFunctorOfResidue
#print axioms S1855SixFieldsMissing_iff
#print axioms S1855SixFieldsMissing_iff_field6

end LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual