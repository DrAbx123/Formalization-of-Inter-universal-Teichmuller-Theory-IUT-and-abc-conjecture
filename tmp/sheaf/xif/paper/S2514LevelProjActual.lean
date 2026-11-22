import tmp.sheaf.xif.paper.S2512FiniteLevelActionActual
import tmp.sheaf.xif.paper.S2513EvalContinuousActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2046G1CyclotomeActual
open LeanFormal.IUT.XiFPaper.S2511ContinuousTwoCocycleActual
open LeanFormal.IUT.XiFPaper.S2512FiniteLevelActionActual
open LeanFormal.IUT.XiFPaper.S2513EvalContinuousActual

namespace LeanFormal.IUT.XiFPaper.S2514LevelProjActual

variable (p : Nat) [Fact (Nat.Prime p)]

lemma S2514ContinuousAction_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : DiscreteContinuousGroupAction G (Otri p)ˣ)
    (g : G) (f : PsiCnsCyclotome p) :
    (KummerCyclotome.continuousAction A).automorphism g f =
      fun q => A.automorphism g (f q) :=
  rfl

lemma S2481Eval_reverse (L : S2481CoeffLimit p) (n : ℕ+) :
    S2481Eval (p := p) (S2481Reverse (p := p) L) n = L.val n := by
  simpa [S2481EvalLimit] using
    congrFun (S2481EvalLimit_reverse_val (p := p) L) n

lemma S2481MulEquiv_val (f : PsiCnsCyclotome p) (n : ℕ+) :
    (S2481MulEquiv (p := p) f).val n = S2481Eval (p := p) f n :=
  rfl

lemma S2481MulEquiv_symm_apply_one_div (L : S2481CoeffLimit p) (n : ℕ+) :
    (S2481MulEquiv (p := p)).symm L
        (Multiplicative.ofAdd (((1 : ℚ) / (n : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
      (L.val n : (Otri p)ˣ) := by
  change S2481Eval (p := p) (S2481Reverse (p := p) L) n = (L.val n : (Otri p)ˣ)
  simpa using congrArg
    (fun x : S2481Roots p (n : ℕ) => (x : (Otri p)ˣ))
    (S2481Eval_reverse (p := p) L n)

lemma S2481Eval_MulEquiv_symm (L : S2481CoeffLimit p) (n : ℕ+) :
    S2481Eval (p := p) ((S2481MulEquiv (p := p)).symm L) n = L.val n := by
  change S2481Eval (p := p) (S2481Reverse (p := p) L) n = L.val n
  exact S2481Eval_reverse (p := p) L n

lemma S2046PsiCnsAction_apply (g : Gv p) (f : PsiCnsCyclotome p) :
    S2046G1PsiCnsAction (p := p) g f =
      fun q => (LocalMLFModelTMPair.monoAnalytic p).unitAction p g (f q) :=
  rfl

lemma S2514Action_eval (g : Gv p) (L : S2481CoeffLimit p) (n : ℕ+) :
    (S2481Action (p := p) g L).val n =
      S2512RootMulAut (p := p) n g (L.val n) := by
  apply Subtype.ext
  change (S2481Eval (p := p)
      (S2046G1PsiCnsAction (p := p) g ((S2481MulEquiv (p := p)).symm L)) n)
    = (((LocalMLFModelTMPair.monoAnalytic p).unitAction p g)
        ((L.val n : S2481Roots p (n : ℕ)) : (Otri p)ˣ))
  rw [S2046PsiCnsAction_apply]
  simp only [S2481Eval]
  rw [S2481MulEquiv_symm_apply_one_div]
  rfl

noncomputable def levelProj (n : ℕ+)
    (c : ContinuousTwoCocycle (S2481ContinuousAction (p := p))) :
    ContinuousTwoCocycle (S2512FiniteLevelAction (p := p) n) :=
  { toFun := fun g h =>
      S2481Eval (p := p) (S2481MulEquiv (p := p).symm (c.toFun g h)) n
    continuous := by
      have h1 : Continuous (fun q : Gv p × Gv p =>
          S2481MulEquiv (p := p).symm (c.toFun q.1 q.2)) :=
        (S2481Homeomorph (p := p)).symm.continuous.comp c.continuous
      exact (S2481Eval_continuous (p := p) n).comp h1
    cocycle := by
      intro g h k
      have hc := congrArg
        (fun x : S2481CoeffLimit p =>
          S2481Eval (p := p) (S2481MulEquiv (p := p).symm x) n)
        (c.cocycle g h k)
      rw [S2481Eval_MulEquiv_symm] at hc
      apply Subtype.ext
      simpa [S2514Action_eval, S2512FiniteLevelAction, S2512RootMulAut,
        map_mul, MulAut.mul_apply] using hc }

end LeanFormal.IUT.XiFPaper.S2514LevelProjActual
end