import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

structure S3128Stage1HDDSourceHullSpec
    (D : S1356HDDSourceRequired (I := I)) : Prop where
  rank_eq : (s1356LatticeOfSource (I := I) D).rank = D.rank
  lattice_eq :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (s1356LatticeOfSource (I := I) D).lattice o v = D.lattice o v
  hull_eq :
    ∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
      (s1356LatticeOfSource (I := I) D).lattice o v =
        (fun x : (i : Fin D.rank) → D.E i =>
          fun i => D.localEquiv v i (x i)) ''
        @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)

theorem S3128Stage1HDDSourceHullSpec_ofSource
    (D : S1356HDDSourceRequired (I := I)) :
    S3128Stage1HDDSourceHullSpec (I := I) D :=
  { rank_eq := rfl
    lattice_eq := fun o v => rfl
    hull_eq := fun o v => D.toS1215_lattice_eq_hull o v }

#check S3128Stage1HDDSourceHullSpec
#check S3128Stage1HDDSourceHullSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecActual