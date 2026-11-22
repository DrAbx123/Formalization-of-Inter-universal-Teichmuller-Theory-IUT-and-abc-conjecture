/-! # Stage-4 host: repo-first prior-art check (§7.9)

Binding rule: before writing a new Lean file, grep exact type/lemma names across
LeanFormal/, Iut/, tmp/local-cft-port/, tmp/archive_*, vendor/promachina/snapshots/,
papers/motizuki_corpus/; report the prior art as file:line decl -> reuse/adapt/none.

This file records the prior-art check for the current stage-4 tasks (theater family,
Fact-prime instance, model Haar/scaling/OriginalInput, unit-region/Haar data).

LABEL: prior-art record (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136PriorArtCheckActual

structure LGPPriorArtRow where
  query : String
  priorArt : String
  decision : String

def lgpPriorArtCheck : List LGPPriorArtRow :=
  [ ⟨"theater-family construction", "LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean:122 sourceHaarActualPrimeStrip, :143 sourceHaarActualTheater, :151 sourceHaarActualPrimeStripEquiv, :213 sourceHaarActualTheaterLink, :224-284 laws, :288 sourceHaarActualTheater_injective, :322 sourceHaarActualFamily", "REUSE (import; do not re-prove)"⟩,
    ⟨"original input / source datum plumbing", "SourceUnitRegionHaarDataActual.lean:346 sourceHaarActualOriginalInput (S : SourceDefinition31Data) : OriginalInput; :357 sourceHaarActual_primeStripAt", "REUSE (our assembled SourceDefinition31Data feeds it)"⟩,
    ⟨"unit-region / Haar data", "SourceUnitRegionHaarDataActual.lean:407 sourceHaarActualUnitRegion, :416 sourceHaarActualData : I.SourceUnitRegionHaarData, :433 unitRegion, :441 sourceHaarActualData_scaling (scaling = 1), :447 nonempty", "REUSE (model unit region exists)"⟩,
    ⟨"SourceUnitRegionHaarData interface", "LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierHaarData.lean:159 structure SourceUnitRegionHaarData (unitRegion, scaling, degreeBound, hull_subset_scaledRegionImage, unitRegion_logDegree_le, scaling_logDegree_nonpos)", "ADAPT (map our LGPUnitRegionInterface onto it)"⟩,
    ⟨"ThetaPilotCarrier type", "LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean:64 def ThetaPilotCarrier", "REUSE (unit-region index type)"⟩,
    ⟨"OriginalInput type", "LeanFormal/IUT/IUTI/Theorem311/SourceOriginalInput.lean:41 structure OriginalInput (initial, family, index_equiv, arithmetic_alignment)", "REUSE"⟩,
    ⟨"Fact prime instance for completionRationalPrime", "LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:28-29 instance completionRationalPrime_fact : Fact (completionRationalPrime place).val.Prime", "REUSE (inferInstance; do not re-derive via .property)"⟩,
    ⟨"model theta packet (q=1 variant)", "SourceUnitRegionHaarDataActual.lean:139 sourceHaarActualThetaPacket = FiniteThetaPacket.ofQ 1; model needs gaussianFiveThetaQ", "ADAPT (our S3136ModelThetaPacketActual keeps gaussianFiveThetaQ; sourceHaarActualThetaPacket noted as alternative)"⟩,
    ⟨"Haar measure provider", "Mathlib MeasureTheory.Measure.addHaar; used at FinitePlaceArithmeticIQHullTransport.lean:107 for product tensor blocks", "REUSE (our lgpNativeHaarFamily built on it)"⟩,
    ⟨"importable tool libraries", "tmp/local-cft-port (Brauer.exists_root, KummerTheory.Mu); Iut/ oleans; vendor snapshots source-only", "REUSE/OBSERVE (Brauer/Kummer already reused; vendor = source reference only)"⟩ ]

theorem lgpPriorArtCheck_length : lgpPriorArtCheck.length = 10 := rfl

#check lgpPriorArtCheck
#check lgpPriorArtCheck_length

end LeanFormal.IUT.XiFPaper.S3136PriorArtCheckActual