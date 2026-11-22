import tmp.sheaf.xif.paper.S2039ActualPsiCns

/-! Consumer check for S2039: the public interface of the actual Psi_cns
construction. -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns

namespace LeanFormal.IUT.XiFPaper.S2039Consumer

/-- Z-hat is an actual commutative ring. -/
example : CommRing Zhat := inferInstance

/-- Int embeds in Z-hat. -/
example : Function.Injective (zhatIntHom : Int →+* Zhat) := zhatIntHom_injective

/-- The source-faithful Kummer map of O^tri_{F_v} is injective. -/
example (p : Nat) [Fact (Nat.Prime p)] :
    Function.Injective (PsiCnsBaseKummer p) :=
  PsiCnsBaseKummer_injective p

/-- The Kummer image of O^tri_{F_v} is O^tri_{F_v}. -/
example (p : Nat) [Fact (Nat.Prime p)] :
    Nonempty (PsiCnsBaseImage p ≃* OtriFv p) :=
  PsiCnsBaseImage_equiv p

/-- Psi_cns is a submonoid of the actual cohomological limit. -/
example (p : Nat) [Fact (Nat.Prime p)] (N : PsiCnsNormalization p) :
    (1 : PsiCnsCohomology p) ∈ PsiCns p N :=
  one_mem_PsiCns p N

/-- The exact content of the source's (d). -/
example (p : Nat) [Fact (Nat.Prime p)] (N : PsiCnsNormalization p) :
    KummerEqualsPsiCns p N ↔
      NormalizationIsValuation p N ∧ PsiCnsExhaustion p N :=
  kummerEquals_iff p N

/-- Psi_cns is O^tri_{F_v} from the two source assertions. -/
example (p : Nat) [Fact (Nat.Prime p)] (N : PsiCnsNormalization p)
    (hval : NormalizationIsValuation p N) (hex : PsiCnsExhaustion p N) :
    Nonempty (PsiCns p N ≃* OtriFv p) :=
  PsiCns_equiv_otriFv p N hval hex

/-- The cyclotomic comparison, characterized on the coefficient modules. -/
example (p : Nat) [Fact (Nat.Prime p)] :
    CyclotomeComparison p ↔ Nonempty (muHatZ p ≃* PsiCnsCyclotome p) :=
  cyclotomeComparison_iff p

#print axioms LeanFormal.IUT.XiFPaper.S2039ActualPsiCns.zhatIntHom_injective
#print axioms LeanFormal.IUT.XiFPaper.S2039ActualPsiCns.PsiCnsBaseKummer_injective
#print axioms LeanFormal.IUT.XiFPaper.S2039ActualPsiCns.PsiCns_equiv_otriFv
#print axioms LeanFormal.IUT.XiFPaper.S2039ActualPsiCns.cyclotomeComparison_iff

end LeanFormal.IUT.XiFPaper.S2039Consumer