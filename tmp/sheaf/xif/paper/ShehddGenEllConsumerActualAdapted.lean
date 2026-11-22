import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import tmp.sheaf.xif.paper.GenEll09IUTIVSection2ConsumerActual
import tmp.sheaf.xif.paper.GenEll10bH6Mzk1WiringActual

/-!
# ShehddGenEllConsumerActualAdapted — GenEll Thm 2.1 / IUT IV §2 / H6 x Mzk1 consumer bundle

STEP 0 prior-art (reuse only; A475 search: GenEll assets found):
* GenEll05Theorem21Actual: CaseI/CaseII, theorem21_i_implies_ii (PROVED direction),
  Theorem21ReductionInputs, Theorem21_ii_implies_i_required (paper-input);
* GenEll09IUTIVSection2ConsumerActual: theorem21_equiv_of_paperInput,
  iutIVSection2_cor23_bdClass, iutIVSection2_abcAll_of_genEllMainReduction;
* GenEll10bH6Mzk1WiringActual: H6Mzk1Witness, h6_genEll_transfer_of_mzk1,
  mzk1_thm25_of_core, h6_mzk1_interface.

This file packages the GenEll Thm 2.1 / IUT IV §2 / H6 x Mzk1 consumer chains as one
interface.  No new assumptions, no sorry/axiom; paper-input directions stay named
(Theorem21_ii_implies_i_required, noncritical Belyi, §3/§4 inputs).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddGenEllConsumerActualAdapted

open LeanFormal.IUT.XiFPaper.GenEll01BasicActual
open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open LeanFormal.IUT.XiFPaper.GenEll08MainReductionActual
open LeanFormal.IUT.XiFPaper.GenEll09IUTIVSection2ConsumerActual
open LeanFormal.IUT.XiFPaper.GenEll10bH6Mzk1WiringActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open NeronModelInfra
open CategoryTheory AlgebraicGeometry

universe u

/-- **PROVED consumer:** GenEll Thm 2.1 as an equivalence, conditional on the named
paper-input direction (ii)=>(i). -/
theorem genEll_theorem21_iff_consumer {X : Type u} (K : Set X)
    (ht logDiff logCond : X → ℝ) (eps : ℝ)
    (hIItoI : CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) :
    CaseI ht logDiff logCond eps ↔ CaseII K ht logDiff logCond eps :=
  theorem21_equiv_of_paperInput K ht logDiff logCond eps hIItoI

/-- **PROVED consumer:** the IUT IV §2 Cor 2.3 BD-class consumer (Thm 1.10 + Cor 2.2
output plus the named GenEll (ii)=>(i) input). -/
theorem genEll_section2_cor23_consumer {X : Type u} (K : Set X)
    (ht logDiff logCond : X → ℝ) (eps : ℝ)
    (thm110Cor22CaseII : CaseII K ht logDiff logCond eps)
    (genEllIItoI : CaseII K ht logDiff logCond eps → CaseI ht logDiff logCond eps) :
    CaseI ht logDiff logCond eps :=
  iutIVSection2_cor23_bdClass K ht logDiff logCond eps thm110Cor22CaseII genEllIItoI

/-- **PROVED consumer:** the ABC-level GenEll main-reduction consumer. -/
theorem genEll_abcAll_consumer
    {theorem21Equiv theorem38 cor43 cor44 abcAll abcGeneralPosition : Prop}
    (hMain : GenEllMainReductionStatement theorem21Equiv theorem38 cor43 cor44
      abcAll abcGeneralPosition)
    (h21 : theorem21Equiv) (h38 : theorem38) (h43 : cor43) (h44 : cor44)
    (hGP : abcGeneralPosition) :
    abcAll :=
  iutIVSection2_abcAll_of_genEllMainReduction hMain h21 h38 h43 h44 hGP

/-- **PROVED consumer:** the combined H6 x Mzk1 interface (H6 transfer + [Mzk1]
Thm 2.5 conclusion under the single GeometricCore named hypothesis). -/
theorem h6_mzk1_interface_consumer {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (w : H6Mzk1Witness PUnit c ε T D) :
    (∃ lowerBound : ℝ, ∀ x : PUnit,
      lowerBound ≤ (1 + w.shadow.epsilon) *
        (w.shadow.logDiff x + w.shadow.logCond x) - w.shadow.height x) ∧
      (∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W) :=
  h6_mzk1_interface c ε T D w

/-- Row record: reused GenEll/H6 assets vs the consumer interface. -/
def genEllConsumerRows : List (String × String × String) :=
  [ ("GenEll Thm 2.1 (i)=>(ii) PROVED", "REUSED PROVED", "GenEll05Theorem21Actual.theorem21_i_implies_ii")
  , ("Thm 2.1 (ii)=>(i) + noncritical Belyi + §3/§4", "NAMED PAPER INPUTS", "Theorem21_ii_implies_i_required / iutIVSection2RemainingPaperInputs")
  , ("IUT IV §2 Cor 2.3 BD-class consumer", "REUSED PROVED (conditional)", "GenEll09.iutIVSection2_cor23_bdClass")
  , ("GenEll ABC-level consumer", "REUSED PROVED (conditional)", "GenEll09.iutIVSection2_abcAll_of_genEllMainReduction")
  , ("H6 x Mzk1 interface (H6 transfer + Thm2.5)", "REUSED PROVED (conditional)", "GenEll10b.h6_mzk1_interface")
  , ("consumer bundle", "COMPOSED PROVED", "genEll_theorem21_iff_consumer, genEll_section2_cor23_consumer, genEll_abcAll_consumer, h6_mzk1_interface_consumer") ]

theorem genEllConsumerRows_length : genEllConsumerRows.length = 6 := rfl

#check genEll_theorem21_iff_consumer
#check genEll_section2_cor23_consumer
#check genEll_abcAll_consumer
#check h6_mzk1_interface_consumer
#check genEllConsumerRows_length

end LeanFormal.IUT.XiFPaper.ShehddGenEllConsumerActualAdapted
end
