import tmp.sheaf.xif.paper.S1300HDDHullDetActual

-- S1356: attempt actual E/image/compact/coordinate/det for
-- S1300HDDHullDetSource using LocalFieldProductHull and HullDeterminant.
-- Actual hull/det donors exist; the source image family E/image and a
-- uniform localEquiv to every place are absent.  Exact first field recorded.
-- No rank-one/arbitrary Set.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Exact first missing field: a uniform family E with ring equivalences to
every 1-column local field. -/
abbrev S1356UniformLocalEquiv (rank : Nat) (E : Fin rank → Type)
    [∀ i, NormedField (E i)] : Type :=
  ∀ v : NumberField.FinitePlace ℚ,
    (i : Fin rank) → E i ≃+* (oneColumnStructure).localField v

/-- Exact S1300 source obligation (no inhabitant). -/
abbrev S1356HDDSourceRequired : Type (v + 1) :=
  S1300HDDHullDetSource (I := I)

/-- Conditional actual: a supplied S1300 source gives the actual hull-based
S1215 lattice via LocalFieldProductHull.hull. -/
noncomputable def s1356LatticeOfSource
    (D : S1300HDDHullDetSource (I := I)) :
    S1215HDDLocalLattice (I := I) :=
  D.toS1215 (I := I)

#check S1356UniformLocalEquiv
#check S1356HDDSourceRequired
#check s1356LatticeOfSource
#check LocalFieldProductHull.hull
#check LocalFieldProductHull.integralSpan_eq_hull
#check S1300ActualHullDetSpec
#check s1300ActualHullDetSpec_holds
#check HullDeterminantLogVolumeFrozenSpec
#check hullDeterminantLogVolumeFrozenSpec_holds
#check DetTensorPowerLogVolumeBookkeeping

end LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual

end