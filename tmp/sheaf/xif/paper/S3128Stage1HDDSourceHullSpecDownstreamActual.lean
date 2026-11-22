import tmp.sheaf.xif.paper.S3128Stage1HDDSourceHullSpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecDownstreamActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDSourceHullSpecDownstream_rank
    (D : S1356HDDSourceRequired (I := I)) :
    (s1356LatticeOfSource (I := I) D).rank = D.rank :=
  (S3128Stage1HDDSourceHullSpec_ofSource (I := I) D).rank_eq

theorem S3128Stage1HDDSourceHullSpecDownstream_lattice
    (D : S1356HDDSourceRequired (I := I))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (s1356LatticeOfSource (I := I) D).lattice o v = D.lattice o v :=
  (S3128Stage1HDDSourceHullSpec_ofSource (I := I) D).lattice_eq o v

theorem S3128Stage1HDDSourceHullSpecDownstream_hull
    (D : S1356HDDSourceRequired (I := I))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (s1356LatticeOfSource (I := I) D).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) :=
  (S3128Stage1HDDSourceHullSpec_ofSource (I := I) D).hull_eq o v

#check S3128Stage1HDDSourceHullSpecDownstream_rank
#check S3128Stage1HDDSourceHullSpecDownstream_lattice
#check S3128Stage1HDDSourceHullSpecDownstream_hull
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecDownstreamActual