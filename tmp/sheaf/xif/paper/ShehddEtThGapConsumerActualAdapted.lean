import tmp.sheaf.xif.paper.Mzk1EtThGapStatementActualAdapted
import tmp.sheaf.xif.paper.Mzk1EtThRealizationConsumerActual

/-!
# ShehddEtThGapConsumerActualAdapted — EtTh realization gap / deep-input consumer

STEP 0 prior-art (reuse only):
* Mzk1EtThGapStatementActualAdapted: EtThGeometricRealization / EtThFrobenioidManifestation /
  EtThActualThetaTransformation (paper-scope rows), EtThRealizationGap bundle and its
  geometricRealization_of projection;
* Mzk1EtThRealizationConsumerActual: EtThRealizationInput package,
  EtThRealizationInput.holds_of_input, EtThThm25ConsumerInputs and
  etThRealization_thm25Consumer_conditional (GeometricCore stays the single named
  hypothesis), etThRealization_holds_of_consumerInputs.

This file gives the consumer-facing bridge between the statement rows and the named deep
realization package: the gap bundle projections in both directions, and the Thm25
consumer input's realization coherence.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddEtThGapConsumerActualAdapted

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1EtThGapStatementActualAdapted
open LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open LeanFormal.IUT.XiFPaper.GenEll08MainReductionActual
open LeanFormal.IUT.XiFPaper.GenEll09IUTIVSection2ConsumerActual

/-- **PROVED consumer:** the EtTh realization gap bundle gives its three row statements. -/
theorem etTh_gap_components {gr fm thetaT : Prop}
    (h : EtThRealizationGap gr fm thetaT) :
    EtThGeometricRealization gr ∧ EtThFrobenioidManifestation fm ∧
      EtThActualThetaTransformation thetaT :=
  ⟨EtThRealizationGap.geometricRealization_of h, h.2.1, h.2.2⟩

/-- **PROVED consumer:** the three row statements reassemble into the gap bundle. -/
theorem etTh_gap_of_components {gr fm thetaT : Prop}
    (h1 : EtThGeometricRealization gr) (h2 : EtThFrobenioidManifestation fm)
    (h3 : EtThActualThetaTransformation thetaT) :
    EtThRealizationGap gr fm thetaT :=
  ⟨h1, h2, h3⟩

/-- **PROVED consumer:** the Thm25 consumer input carries a coherent EtTh realization
package (all rows + coherence). -/
theorem etTh_realization_holds {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (I : EtThThm25ConsumerInputs c ε T D) : I.realization.holds :=
  etThRealization_holds_of_consumerInputs c ε T D I

/-- Row record: reused gap/realization assets vs consumer bridge. -/
def etThGapConsumerRows : List (String × String × String) :=
  [ ("EtTh realization gap bundle + projection", "REUSED DEF/PROVED", "Mzk1EtThGapStatementActualAdapted.EtThRealizationGap / geometricRealization_of")
  , ("named deep realization package holds", "REUSED PROVED", "EtThRealizationInput.holds_of_input")
  , ("gap bundle => three row statements", "COMPOSED PROVED", "etTh_gap_components")
  , ("three rows => gap bundle", "COMPOSED PROVED", "etTh_gap_of_components")
  , ("Thm25 consumer input => coherent realization", "COMPOSED PROVED", "etTh_realization_holds")
  , ("GeometricCore conditional Thm25 consumer", "REUSED CONDITIONAL", "etThRealization_thm25Consumer_conditional (GeometricCore remains named)") ]

theorem etThGapConsumerRows_length : etThGapConsumerRows.length = 6 := rfl

#check etTh_gap_components
#check etTh_gap_of_components
#check etTh_realization_holds
#check etThGapConsumerRows_length

end LeanFormal.IUT.XiFPaper.ShehddEtThGapConsumerActualAdapted
end
