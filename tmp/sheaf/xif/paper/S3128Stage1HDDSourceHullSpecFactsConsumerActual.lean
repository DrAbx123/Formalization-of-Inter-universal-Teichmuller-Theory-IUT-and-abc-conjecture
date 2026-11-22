import tmp.sheaf.xif.paper.S3128Stage1HDDSourceHullSpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecFactsConsumerActual
universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

theorem S3128Stage1HDDSourceHullSpecFacts
    (D : S1356HDDSourceRequired (I := I)) :
    (s1356LatticeOfSource (I := I) D).rank = D.rank
      ∧ (∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
          (s1356LatticeOfSource (I := I) D).lattice o v = D.lattice o v)
      ∧ (∀ (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ),
          (s1356LatticeOfSource (I := I) D).lattice o v =
            (fun x : (i : Fin D.rank) → D.E i =>
              fun i => D.localEquiv v i (x i)) ''
            @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)) :=
  let S := S3128Stage1HDDSourceHullSpec_ofSource (I := I) D
  ⟨S.rank_eq, S.lattice_eq, S.hull_eq⟩

#check S3128Stage1HDDSourceHullSpecFacts
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDSourceHullSpecFactsConsumerActual