import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutSpecActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

structure S3128Stage1HDDReadoutSpec (D : S1300HDDHullDetSource I) : Prop where
  rank_eq : (D.toS1215 (I := I)).rank = D.rank
  lattice_eq : ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
    (D.toS1215 (I := I)).lattice o v = D.lattice o v
  hull_eq : ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
    (D.toS1215 (I := I)).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)
  frozen : HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}

theorem S3128Stage1HDDReadoutSpec_ofSource
    (D : S1300HDDHullDetSource I) :
    S3128Stage1HDDReadoutSpec D :=
  { rank_eq := rfl
    lattice_eq := fun o v => D.toS1215_lattice o v
    hull_eq := fun o v => D.toS1215_lattice_eq_hull o v
    frozen := s1385FrozenSpec_actual }

#check S3128Stage1HDDReadoutSpec
#check S3128Stage1HDDReadoutSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDReadoutSpecActual