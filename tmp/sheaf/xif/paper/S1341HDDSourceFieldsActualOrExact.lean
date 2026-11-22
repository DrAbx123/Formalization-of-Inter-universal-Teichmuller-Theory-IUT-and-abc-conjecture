import tmp.sheaf.xif.paper.S1300HDDHullDetActual

-- S1341: try actual E/localEquiv/image/det for S1300HDDHullDetSource.
-- Actual donors exist for hull/det (LocalFieldProductHull, HullDeterminant),
-- but no uniform E/localEquiv can be built because the 1-column local
-- fields depend on the place v.  Exact first field recorded; no rank-one/
-- arbitrary Set.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1341HDDSourceFieldsActualOrExact

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Exact first missing field: a uniform family E with a ring equivalence to
every 1-column local field at every place. -/
abbrev S1341UniformLocalEquiv (rank : Nat) (E : Fin rank → Type)
    [∀ i, NormedField (E i)] : Type :=
  ∀ v : NumberField.FinitePlace ℚ,
    (i : Fin rank) → E i ≃+* (oneColumnStructure).localField v

/-- Exact S1300 source type, as the first outstanding HDD object. -/
abbrev S1341HDDSourceRequired : Type (v + 1) :=
  S1300HDDHullDetSource (I := I)

/-- Conditional actual: once a S1300 source is supplied, the actual
LocalFieldProductHull hull gives the S1215 HDD local lattice. -/
noncomputable def s1341LatticeOfSource (D : S1300HDDHullDetSource (I := I)) :
    S1215HDDLocalLattice (I := I) :=
  D.toS1215 (I := I)

#check S1341UniformLocalEquiv
#check S1341HDDSourceRequired
#check s1341LatticeOfSource
#check S1300HDDHullDetSource
#check S1300HDDHullDetSource.toS1215
#check LocalFieldProductHull.hull
#check LocalFieldProductHull.integralSpan_eq_hull
#check HullDeterminantLogVolumeFrozenSpec
#check DetTensorPowerLogVolumeBookkeeping

end LeanFormal.IUT.XiFPaper.S1341HDDSourceFieldsActualOrExact

end