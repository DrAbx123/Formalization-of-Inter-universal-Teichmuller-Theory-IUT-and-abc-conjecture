import tmp.sheaf.xif.paper.S3128AverageActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjHa0Actual

variable {G : Type} [Group G] [Fintype G]
variable {A B : Type} [CommRing A] [MulSemiringAction G A]
  [CommRing B] [MulSemiringAction G B]

theorem S3128Surj_ha0 [Algebra A B]
    (halg : forall (g : G) (a : A),
      g • algebraMap A B a = algebraMap A B (g • a))
    {a0 : A} {f : A} {n : Nat} {s : B}
    (hm : s * algebraMap A B (f ^ n) = algebraMap A B a0)
    (hs : forall h : G, h • s = s) (h : G) :
    algebraMap A B (h • a0) = s * algebraMap A B ((h • f) ^ n) := by
  have hh := congrArg (fun x : B => h • x) hm
  simpa [smul_mul', halg, smul_pow, hs] using hh.symm

#check S3128Surj_ha0

end LeanFormal.IUT.XiFPaper.S3128SurjHa0Actual
end