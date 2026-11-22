import tmp.sheaf.xif.paper.S2433ReverseEvalActual

noncomputable section
universe u

namespace LeanFormal.IUT.XiFPaper.S2511ContinuousTwoCocycleActual

open LeanFormal.IUT

/-- A jointly continuous group 2-cocycle for a continuous action. -/
structure ContinuousTwoCocycle
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (action : Iut.ContinuousGroupAction G A) where
  toFun : G → G → A
  continuous : Continuous (fun p : G × G => toFun p.1 p.2)
  cocycle : ∀ g h k : G,
    toFun g h * toFun (g * h) k =
      action.act g (toFun h k) * toFun g (h * k)

namespace ContinuousTwoCocycle

variable
    {G A : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {action : Iut.ContinuousGroupAction G A}

@[ext]
theorem ext {c d : ContinuousTwoCocycle action}
    (h : ∀ g h', c.toFun g h' = d.toFun g h') : c = d := by
  cases c with
  | mk cf cc cy =>
    cases d with
    | mk df dc dy =>
      simp only at h
      have hf : cf = df := funext (fun g => funext (fun h' => h g h'))
      subst hf
      exact congrArg (fun q => ({ toFun := cf, continuous := cc, cocycle := q } : ContinuousTwoCocycle action))
        (Subsingleton.elim cy dy)

end ContinuousTwoCocycle

end LeanFormal.IUT.XiFPaper.S2511ContinuousTwoCocycleActual
end