import tmp.sheaf.xif.paper.S2480QiActual
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2480QiActual

namespace LeanFormal.IUT.XiFPaper.S2535AdjoinRootAlgebraMapActual

universe u

theorem S2535_commutes_adjoinRoot
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (x : ℚ) :
    f (algebraMap F A (AdjoinRoot.of (X ^ 2 + 1) x)) =
      algebraMap F B (AdjoinRoot.of (X ^ 2 + 1) x) :=
  f.commutes _

theorem S2535_commutes_root
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) :
    f (algebraMap F A (AdjoinRoot.root (X ^ 2 + 1))) =
      algebraMap F B (AdjoinRoot.root (X ^ 2 + 1)) :=
  f.commutes _

#check S2535_commutes_adjoinRoot
#check S2535_commutes_root
#print axioms S2535_commutes_adjoinRoot
end LeanFormal.IUT.XiFPaper.S2535AdjoinRootAlgebraMapActual
end