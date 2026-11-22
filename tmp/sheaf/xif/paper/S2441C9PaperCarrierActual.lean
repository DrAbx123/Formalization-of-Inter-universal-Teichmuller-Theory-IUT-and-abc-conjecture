import tmp.sheaf.xif.paper.S1979QPilotStripFromDivisorActual

/-! # S2441: actual fixed-Type paper q-pilot carrier and piloted T5 binding

Builds on S1979's actual piloted strip: a fixed-Type carrier (no Prop-valued
`paper_*_identification` slots), the actual q_v generators, the Def 3.8(i)
divisor, and the piloted identification with the reduced sourceQPilotStrip
anchor.  The literal paper `O^▷(A) ⊆ O^◃(A)` pro-object generators are still
the exact missing object; no vacuous self-equality is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

local instance s2441GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2441FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual

/-- Fixed-Type paper q-pilot carrier: the piloted strip with its actual q_v
generators, the associated Def 3.8(i) divisor, and the divisor identification.
No Props; all fields are actual data/equalities. -/
structure S2441PaperQPilotCarrier (D : S1895PaperInput) where
  pilotedStrip :
    PilotedFTimesMuPrimeStrip PaperV (paperInput D).initial.badPlaces
  pilotedStrip_eq : pilotedStrip = paperQPilotPilotedStrip D
  pilotObject : IUTIVArithmeticDivisor (PaperFmod D)
  pilotObject_eq :
    pilotObject = associatedPilotObject D pilotedStrip
  pilotObject_eq_paper : pilotObject = paperQPilotDivisor D

noncomputable def s2441PaperQPilotCarrier (D : S1895PaperInput) :
    S2441PaperQPilotCarrier D where
  pilotedStrip := paperQPilotPilotedStrip D
  pilotedStrip_eq := rfl
  pilotObject := associatedPilotObject D (paperQPilotPilotedStrip D)
  pilotObject_eq := rfl
  pilotObject_eq_paper := associatedPilotObject_paperStrip D

/-- The actual generator value at each bad place is log q_v. -/
theorem s2441_generator_value_eq_log (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    pilotGeneratorRealifiedValue (paperQPilotPilotedStrip D) b =
      Real.log (paperQV D b) :=
  paperQPilotPilotedStrip_value D b

/-- The associated divisor has the actual bad-q absolute log degree. -/
theorem s2441_pilotObject_deg (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D)
      (associatedPilotObject D (paperQPilotPilotedStrip D)) =
        sourceBadQAbsLog (paperInput D).initial :=
  associatedPilotObject_deg_eq_source D

/-- Fixed-Type piloted T5 binding: actual paper piloted strip + its reduced
sourceQPilotStrip anchor + the q_v-compatible piloted identification. -/
structure S2441PilotedT5Binding (D : S1895PaperInput) where
  carrier : S2441PaperQPilotCarrier D
  reducedStrip : SourceFTimesMuPrimeStrip PaperV
  reducedStrip_eq : reducedStrip = reducedQPilotTimesMu D
  sourceAnchor : FPrimeStrip PaperV
  sourceAnchor_eq :
    sourceAnchor = sourceQPilotStrip (S1895PaperO D).boundary
  projection_eq :
    carrier.pilotedStrip.toSourceFTimesMuPrimeStrip = reducedStrip
  pilotedIdentification :
    PilotedQPilotAnchorIdentification D carrier.pilotedStrip

noncomputable def s2441PilotedT5Binding (D : S1895PaperInput) :
    S2441PilotedT5Binding D where
  carrier := s2441PaperQPilotCarrier D
  reducedStrip := reducedQPilotTimesMu D
  reducedStrip_eq := rfl
  sourceAnchor := sourceQPilotStrip (S1895PaperO D).boundary
  sourceAnchor_eq := rfl
  projection_eq := rfl
  pilotedIdentification :=
    paperQPilotPilotedIdentification D

/-- The binding uses the actual q_v generators, not the trivial generator. -/
theorem s2441_binding_generator_value (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    pilotGeneratorRealifiedValue
        (s2441PilotedT5Binding D).carrier.pilotedStrip b =
      Real.log (paperQV D b) :=
  s2441_generator_value_eq_log D b

/-- The associated pilot object of the binding is the actual q-pilot divisor. -/
theorem s2441_binding_pilotObject (D : S1895PaperInput) :
    (s2441PilotedT5Binding D).carrier.pilotObject =
      paperQPilotDivisor D :=
  (s2441PilotedT5Binding D).carrier.pilotObject_eq_paper

/-- The actual bad q-parameter is nonzero. -/
theorem s2441_paperQV_ne_zero (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    paperQV D b ≠ 0 :=
  ne_of_gt (paperQV_pos D b)

/-- Exact paper-level q-pilot scalar normalization missing: the paper normalized
value is `-rootFactor * weightedMagnitude`, with the IUT-IV `1/(2l)` factor;
the weighted magnitude still needs the local degrees, Rem 3.1.1(ii) weights and
procession average.  No inhabitant is asserted. -/
structure S2441QPilotPaperNormalizationRequired (D : S1895PaperInput) where
  paperNormalized : Real
  rootFactor : Real
  rootFactor_eq : rootFactor = (2 * (D.l.value : Real))⁻¹
  weightedMagnitude : Real
  paperNormalized_eq : paperNormalized = -rootFactor * weightedMagnitude
  candidate_eq_paper :
    sourceQPilotSignedLog (paperInput D).initial = paperNormalized

/-- Concrete normalization computed from the actual q_v/orders: the source
q-pilot signed log is `-order_C3 * log 5`, i.e. the paper concrete scalar. -/
theorem s2441_concrete_normalization (D : S1895PaperInput) :
    sourceQPilotSignedLog (paperInput D).initial =
      -((S1487Cand.order : Real) * Real.log 5) := by
  rw [← paperQPilotLogVolume_eq_signedLog D,
    paperQPilotLogVolume_eq_orderC3 D]

/-- The concrete q-pilot divisor degree is the same `order_C3 * log 5`. -/
theorem s2441_concrete_divisor_deg (D : S1895PaperInput) :
    IUTIVArithmeticDivisor.deg (F := PaperFmod D)
      (paperQPilotDivisor D) =
        (S1487Cand.order : Real) * Real.log 5 := by
  rw [paperQPilotDivisor_deg_eq_source]
  have h := s2441_concrete_normalization D
  rw [sourceQPilotSignedLog] at h
  linarith

#check S2441PaperQPilotCarrier
#check s2441PaperQPilotCarrier
#check s2441_generator_value_eq_log
#check s2441_pilotObject_deg
#check S2441PilotedT5Binding
#check s2441PilotedT5Binding
#check s2441_binding_generator_value
#check s2441_binding_pilotObject
#check s2441_paperQV_ne_zero
#check S2441QPilotPaperNormalizationRequired
#check s2441_concrete_normalization
#check s2441_concrete_divisor_deg

end LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
end
