import tmp.sheaf.xif.paper.S2026EffectivityReassemblyActual
import tmp.sheaf.xif.paper.S1985SiteLiftNaturalityActual
import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual

/-! # S2042: D6 effectivity consumed; remaining geometric half of S1864(c)

S2026 proves the iso-comma effectivity/stack/effectivity-all targets with no
sorryAx (checked by #print axioms).  S1985 reduces S1864's pseudopullback
stack statement to `S1985ApexData`, whose first field was the iso-comma stack
condition.  That field is now supplied by S2026, so the remaining geometric
half is exactly:

* `finiteEtale : EtaleStackFiniteEtaleMorphism (structureMap f g)`;
* `structureMap_eq' : Iso (vcomp (toB f g) B.map) (structureMap f g)`;
* the lift-compatibility 2-isomorphism `liftCommutes`;
* the lift uniqueness `uniq`.

This file removes the stack field from the apex-data obligation and records
the exact remaining fields.  It does not fake finite-etale or the 2-isomorphism.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual

open LeanFormal.IUT
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open CategoryTheory

universe u

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

/-- The iso-comma stack field is now actual, from S2026. -/
theorem S2042IsoCommaStack :
    (sitePseudofunctor f g).IsStack (SchemeOverField.etaleTopology S1726K) :=
  S2026IsoCommaStack f g

/-- The iso-comma stack object with its actual S2026 IsStack proof. -/
noncomputable def S2042IsoCommaStackObj : EtaleStackOverField S1726K where
  fiber := sitePseudofunctor f g
  isStack := S2042IsoCommaStack (f := f) (g := g)

/-- The remaining geometric fields of `S1985ApexData`, with the stack field
removed. -/
structure S2042ApexRemaining {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) where
  finiteEtale : EtaleStackFiniteEtaleMorphism
    (source := S2042IsoCommaStackObj (f := f) (g := g))
    (target := S1726Orbicurve.stack) (structureMap f g)
  structureMap_eq' : Iso (Pseudofunctor.StrongTrans.vcomp (toB f g) B.map)
    (structureMap f g)
  liftCommutes : ∀ (W : S1728Cover) (c : S1832Bicone f g W),
    Iso (Pseudofunctor.StrongTrans.vcomp (liftSite (f := f) (g := g) c)
      (structureMap f g)) W.map
  uniq : ∀ (W : S1728Cover) (c : S1832Bicone f g W)
    (h : Pseudofunctor.StrongTrans W.source.fiber (sitePseudofunctor f g))
    (_hmap : Iso (Pseudofunctor.StrongTrans.vcomp h (structureMap f g)) W.map),
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA.map) →
    Nonempty (Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB.map) →
    Nonempty (Iso h (liftSite (f := f) (g := g) c))

/-- S1985 apex data from the remaining geometric fields, with the stack field
filled by the actual S2026 theorem. -/
noncomputable def S2042ApexDataOfRemaining
    (R : S2042ApexRemaining f g) :
    S1985ApexData f g where
  isStack := S2042IsoCommaStack (f := f) (g := g)
  finiteEtale := R.finiteEtale
  structureMap_eq' := R.structureMap_eq'
  liftCommutes := R.liftCommutes
  uniq := R.uniq

/-- Exact remaining geometric-half obligation. -/
def S2042FirstMissingGeometricHalf : Prop :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    Nonempty (S2042ApexRemaining f g)

/-- The remaining geometric half suffices for S1864's first missing statement. -/
theorem S2042FirstMissingGeometricHalf_sufficient
    (h : S2042FirstMissingGeometricHalf) : S1864FirstMissingPseudopullbackStack := by
  intro A B C f g
  exact ⟨S1985ObligationOf (S2042ApexDataOfRemaining
    (Classical.choice (h A B C f g)))⟩

#print axioms S2042IsoCommaStack
#print axioms S2042ApexDataOfRemaining
#print axioms S2042FirstMissingGeometricHalf_sufficient

end LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual

end
