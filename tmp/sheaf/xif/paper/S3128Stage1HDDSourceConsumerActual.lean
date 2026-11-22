import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDSource_rank
    (D : S1356HDDSourceRequired (I := I)) :
    (s1356LatticeOfSource (I := I) D).rank = D.rank := rfl

theorem S3128Stage1HDDSource_lattice
    (D : S1356HDDSourceRequired (I := I))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (s1356LatticeOfSource (I := I) D).lattice o v = D.lattice o v := rfl

theorem S3128Stage1HDDSource_lattice_eq_hull
    (D : S1356HDDSourceRequired (I := I))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (s1356LatticeOfSource (I := I) D).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  D.toS1215_lattice_eq_hull o v

#check S3128Stage1HDDSource_rank
#check S3128Stage1HDDSource_lattice
#check S3128Stage1HDDSource_lattice_eq_hull
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceConsumerActual