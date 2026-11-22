import tmp.sheaf.xif.paper.S2016KummerEquivarianceActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2016KummerEquivarianceActual

/-! Consumer: (M7) of S2011, on the literal carriers. -/

example (p : Nat) [Fact (Nat.Prime p)] (g : LocalAbsoluteGalois p) (a : Otri p) :
    PsiCnsKummer p ((monoAnalytic p).action p g a) =
      germAction p g (PsiCnsKummer p a) :=
  PsiCnsKummer_equivariant p g a

example (p : Nat) [Fact (Nat.Prime p)] (g : LocalAbsoluteGalois p) (a : Otri p) :
    PsiCnsKummer p (LocalIntegralMonoid.galoisAction p g a) =
      germAction p g (PsiCnsKummer p a) :=
  PsiCnsKummer_galoisAction p g a

example (p : Nat) [Fact (Nat.Prime p)] (g h : LocalAbsoluteGalois p) (a : Otri p) :
    PsiCnsKummer p ((monoAnalytic p).action p (g * h) a) =
      germAction p g (germAction p h (PsiCnsKummer p a)) := by
  rw [PsiCnsKummer_equivariant p (g * h) a, germAction_group_mul]

example (p : Nat) [Fact (Nat.Prime p)] (g h : LocalAbsoluteGalois p) (a : Otri p) :
    PsiCnsKummer p ((monoAnalytic p).action p (g * h) a) =
      germAction p g (PsiCnsKummer p ((monoAnalytic p).action p h a)) := by
  rw [PsiCnsKummer_equivariant p (g * h) a, germAction_group_mul,
    ← PsiCnsKummer_equivariant p h a]

example (p : Nat) [Fact (Nat.Prime p)] (g : LocalAbsoluteGalois p)
    {x : PsiCnsCohomology p} (hx : x ∈ PsiCnsKummerImage p) :
    germAction p g x ∈ PsiCnsKummerImage p :=
  germAction_mem_kummerImage p g hx

#print axioms PsiCnsKummer_equivariant
#print axioms PsiCnsKummer_galoisAction
#print axioms transportRealization_germ
