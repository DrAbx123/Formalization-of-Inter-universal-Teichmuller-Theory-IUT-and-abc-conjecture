import tmp.sheaf.xif.paper.S2089FiniteAbelianSubextensionActual
import tmp.sheaf.xif.paper.S2027LocalArtinActual
import Reciprocity.ProfiniteCompletion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046M2CompletionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual
open CategoryTheory ProfiniteGrp

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p)

/-- PadicField's profinite-completion Artin isomorphism, transported through
/-- S2089 and S2027 to the topological abelianization. -/
noncomputable def S2046CompletionEquiv :
    ProfiniteCompletion.completion (GrpCat.of (localField p U)ˣ) ≃*
      TopologicalAbelianization (localGaloisGroup p U) :=
  (PadicField.artinCompletionEquiv (p := p) (K := localField p U)
    (Ω := AlgebraicClosure ℚ_[p])).toMulEquiv.trans
    ((galoisGroupEquiv U).trans (galoisGroupMaximalAbelian p U).symm)

/-- Exact completion-torsion input: torsion of the profinite completion of
/-- K^x is the roots-of-unity subgroup. -/
abbrev S2046TorsionCompletionRequired : Type :=
  mu p U ≃* CommGroup.torsion
    (ProfiniteCompletion.completion (GrpCat.of (localField p U)ˣ))

/-- Exact M2a torsion input, the target of the Artin equivalence. -/
abbrev S2046M2TorsionRequired : Type :=
  mu p U ≃* CommGroup.torsion
    (TopologicalAbelianization (localGaloisGroup p U))

/-- Exact M2c carrier comparison input. -/
abbrev S2046M2CarrierRequired : Type :=
  CommGroup.torsion (Abelianization ↥U) ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))

/-- Conditional LocalArtinSourceData from the two exact inputs. -/
noncomputable def S2046LocalArtinSourceDataOf
    (hartin : ∀ U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p,
      S2046M2TorsionRequired (p := p) U)
    (hcarrier : ∀ U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p,
      S2046M2CarrierRequired (p := p) U) : LocalArtinSourceData p where
  artin := hartin
  carrier := hcarrier

#check S2046CompletionEquiv
#check S2046TorsionCompletionRequired
#check S2046M2TorsionRequired
#check S2046LocalArtinSourceDataOf
#print axioms S2046CompletionEquiv
#print axioms S2046LocalArtinSourceDataOf

end LeanFormal.IUT.XiFPaper.S2046M2CompletionActualAdapted

end