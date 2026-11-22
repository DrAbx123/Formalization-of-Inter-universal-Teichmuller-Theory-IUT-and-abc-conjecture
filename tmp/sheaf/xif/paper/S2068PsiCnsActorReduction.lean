import tmp.sheaf.xif.paper.S2038PaperOActual
import tmp.sheaf.xif.paper.S2039ActualPsiCns
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2038PaperOActual
namespace LeanFormal.IUT.XiFPaper.S2068PsiCnsActorReduction
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual cohomological Psi_cns monoid, conditional on the normalization. -/
abbrev S2068PsiCns (N : PsiCnsNormalization p) : Type :=
  PsiCns p N
def S2068PsiCnsOne (N : PsiCnsNormalization p) : S2068PsiCns p N :=
  ⟨1, one_mem_PsiCns p N⟩
/-- Conditional actual identification Psi_cns = O^tri_{F_v}. -/
theorem S2068PsiCns_equiv_otriFv (N : PsiCnsNormalization p)
    (hval : NormalizationIsValuation p N) (hex : PsiCnsExhaustion p N) :
    Nonempty (S2068PsiCns p N ≃* OtriFv p) :=
  PsiCns_equiv_otriFv p N hval hex
/-- Exact missing (M4): the normalization is not constructed. -/
abbrev S2068M4NormalizationRequired : Prop := NormalizationMissing p
/-- Exact missing (d): normalization + exhaustion. -/
abbrev S2068Cor110bRequired : Prop := Cor110bKummerIdentification p
/-- The group-theoretic algorithm data of IUT II Example 1.8(iii)-(iv). -/
structure S2068GroupAlgorithm where
  alg : ProfiniteGrp → Type
  [commMonoidAlg : ∀ G : ProfiniteGrp, CommMonoid (alg G)]
  algMap : ∀ {G H : ProfiniteGrp}, G ≃* H → alg G ≃* alg H
/-- Assembly data: the algorithm plus its evaluation/action at the paper places. -/
structure S2068OUnitsMuActorAssembly (l : PrimeGeFive)
    (F : FPsiPrimeStrip l) extends S2068GroupAlgorithm where
  actor_equiv_local : ∀ v : S1951KummerEvaluationSquareActual.PaperV,
    Nonempty (alg (@localAbsoluteGaloisProfinite v.1 ⟨v.prime⟩) ≃* LocalOFieldUnitsMuAt v)
  action : ∀ v : S1951KummerEvaluationSquareActual.PaperV,
    @LocalAbsoluteGalois v.1 ⟨v.prime⟩ →*
      MulAut (alg (@localAbsoluteGaloisProfinite v.1 ⟨v.prime⟩))
/-- Conditional assembly: the algorithm data gives the S2038 O^×mu actor. -/
noncomputable def S2068OUnitsMuActorOfAssembly {l : PrimeGeFive}
    {F : FPsiPrimeStrip l} (A : S2068OUnitsMuActorAssembly l F) :
    OUnitsMuActor l F where
  alg := A.alg
  commMonoidAlg := A.commMonoidAlg
  algMap := A.algMap
  actor := fun v => A.alg (@localAbsoluteGaloisProfinite v.1 ⟨v.prime⟩)
  commMonoidActor := fun v => A.commMonoidAlg _
  actor_eq := fun v => rfl
  actor_equiv_local := A.actor_equiv_local
  action := A.action
#check S2068PsiCnsOne
#check S2068PsiCns_equiv_otriFv
#check S2068M4NormalizationRequired
#check S2068Cor110bRequired
#check S2068GroupAlgorithm
#check S2068OUnitsMuActorAssembly
#check S2068OUnitsMuActorOfAssembly
end LeanFormal.IUT.XiFPaper.S2068PsiCnsActorReduction
end
