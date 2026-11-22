/-
  # SHE transport obligations S2 / S3 / S4 / G1: conditional supply layer

  Companion of `SourceSHETransportLaws.lean` (the simultaneity square and its
  transport laws).  This module attacks the four explicitly-open fields of the
  Card-SHE assembly recorded in
  `logs/coordination/outsider-survey-transport-20261016.md`, section 16.4:

  * (S2/G1) `FPrimeStripEquiv.toLink`: the forgetful map from an equivalence
    representative to the underlying fiber link, with its pointwise laws.
    Bridge from the reduced Remark-3.10.2 square `SourceKummerEvaluationSquare`
    (whose Kummer legs carry the `x`-mu unit layer through `SourceKummerArrow`
    and whose horizontals carry the evaluation unit portion through
    `SourceEvaluationArrow`) to the link-level SHE square
    `SourceSimultaneousHolomorphicExpression`, packaged as
    `SourceSHESquareSupply` with per-leg upgrade records.  The condition is
    explicit: an inhabitant of `SourceKummerEvaluationSquare`.  What the upgrade
    records *demand* (rather than derive) is exactly the times-mu / full-poly
    data whose non-derivability from the `LinkSpan` shell is the recorded G1
    negative result (`ProbeCardIPLG1Verdict.lean`, SHA D660C2B4...; report
    section 15.3) -- cited here, not re-proved.
  * (S3) `SourceOneColumnLabelBinding`: packaging of the proved fixed
    one-column projections (SourceSharedBoundary.lean) together with the new
    theorem that the `InitialThetaArithmeticData` is constant along the fixed
    column (`oneColumnTheater_arithmetic`).  The 1,o ring/scheme layer itself
    is NOT constructed here; it is tracked by the reduced card
    `IUT-III.source-arithmetic-holomorphic-landing`
    (SourceArithmeticHolomorphicLanding.lean, Card AS) and its pending
    evidence card `IUT-III.source-SHE-landing-evidence`.
  * (S4) `SourceHullExpressionSupply`: the value-level readout supply for the
    two SHE composites; the condition is explicit (both readouts equal the
    theta-pilot image), and once supplied both readouts provably lie in the
    source holomorphic hull (`SourceImageHull.lean`).  The nondegeneracy input
    (compactness of `1,oU` / log-volume) is outside both the hull form and this
    record; the recorded negative boundary is `literalHullInterface_impossible`
    (SourceImageHull.lean), cited, not re-proved.

  ## Reductions (explicit)

  * R1. SHE is read in the link-level reduction of
    `SourceSHETransportLaws.lean`; the bridge consumes the reduced record
    `SourceKummerEvaluationSquare` (a commuting square of isomorphism
    representatives, Remark 3.10.2), not the paper's full structure.
  * R2. The Kummer-arrow "weight" record of DSH-F API-3 is NOT modeled; only
    the unit layer (`SourceTimesMuKummerLayer` inside `SourceKummerArrow`) is
    carried.  The strip-level `LabelledKummerIso.label` of
    `SourceFaithfulBoundary.lean:196-208` acts on `Choice` carriers and is not
    lifted here.
  * R3. S3 binds the theater-family arithmetic data to the fixed column; it
    does not construct the label "1,o" itself.
  * R4. S4 reads are value-monoid level (`ThetaPilotPoint`); no output strip is
    constructed, and the nondegeneracy is not claimed.

  ## Consumers

  `StepXIContract.she` / `she_evidence` (Contract.lean:38/:41;
  ParametricStepXI.lean:36/:39) and the finite bridge slot
  `FiniteStepXILinkEvidence.she` / `she_evidence`
  (FiniteCertificateBridge.lean).  A consumer with an inhabitant `W` of
  `SourceSHESquareSupply` sets `she := W.square.sheStatement` and obtains the
  evidence from `W.sheStatement_evidence` (or through `W.sheSlot_evidence`
  when the slot is a named `StepXIContract` field equated to the statement).

  ## Paper locations

  IUT III, Remark 3.11.1, (iii) (SHE; PDF p. 161); Remark 3.10.2 (the
  conjugation square); Corollary 3.12, proof, Steps (xi-b) (PDF p. 181) and
  (xi-c) (PDF p. 182); Remark 3.9.5, (i), (ii) (hulls).  DSH-F report
  `tmp/dsh-card-ipl-she-apt-20261016/REPORT.md`, sections 2.2 (S1-S5) and 4
  (API-3, API-5).
-/

import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportLaws
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSharedBoundary
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

namespace LeanFormal.IUT

universe ua uv upi umon ui uG

noncomputable section

variable {V : Type uv}

/-! ## 1. The forgetful link of an equivalence representative (S2 base) -/

namespace FPrimeStripEquiv

variable {F F' : FPrimeStrip.{umon, uv, upi} V}

/-- The fiber link underlying an equivalence representative: the index map is the
identity and the three fiber equivalences are read as monoid homomorphisms.  This is
the transport between the equivalence-representative level used by the Remark-3.10.2
records and the link level used by the SHE square. -/
def toLink (phi : FPrimeStripEquiv F F') : FPrimeStripLink F F' where
  index := id
  mapPi := fun v => (phi.isoPi v).toMonoidHom
  mapG := fun v => (phi.isoG v).toMonoidHom
  mapMon := fun v => (phi.isoMon v).toMonoidHom
  compatProj := fun v => phi.compatProj v
  compatAction := fun v => phi.compatAction v
  compatDegree := fun v => phi.compatDegree v

@[simp] theorem toLink_index (phi : FPrimeStripEquiv F F') :
    phi.toLink.index = id := rfl

@[simp] theorem toLink_mapPi_apply (phi : FPrimeStripEquiv F F') (v : V)
    (x : F.toDPrimeStrip.Pi v) :
    phi.toLink.mapPi v x = phi.isoPi v x := rfl

@[simp] theorem toLink_mapG_apply (phi : FPrimeStripEquiv F F') (v : V)
    (x : F.G v) :
    phi.toLink.mapG v x = phi.isoG v x := rfl

@[simp] theorem toLink_mapMon_apply (phi : FPrimeStripEquiv F F') (v : V)
    (x : F.Mon v) :
    phi.toLink.mapMon v x = phi.isoMon v x := rfl

end FPrimeStripEquiv

/-! ## 2. Per-leg upgrade records (S2 / G1 supplies) -/

/-- S2/G1 conditional supply for an evaluation-type leg: the leg is the underlying
link of a source evaluation arrow (full-poly representative plus the Card-EV
`(-)^triangleright-x-mu` unit portion).  The times-mu data is demanded as a field,
not derived (G1 negative result). -/
structure SourceEvaluationLegUpgrade (G : Type uG) [Group G] [TopologicalSpace G]
    {A B : FPrimeStrip.{umon, uv, upi} V} (leg : FPrimeStripLink A B) where
  /-- the source evaluation arrow over this leg -/
  arrow : Theorem311Source.SourceEvaluationArrow G A B
  /-- the leg is exactly the arrow's underlying link -/
  leg_eq : arrow.stripIso.toLink = leg

/-- S2/G1 conditional supply for a Kummer-type leg in the forward direction: the leg
is the underlying link of a source Kummer arrow, i.e. carries the `x`-mu unit layer
(which units the isomorphism acts on). -/
structure SourceKummerLegUpgrade (G : Type uG) [Group G] [TopologicalSpace G]
    {A B : FPrimeStrip.{umon, uv, upi} V} (leg : FPrimeStripLink A B) where
  /-- the source Kummer arrow over this leg -/
  arrow : Theorem311Source.SourceKummerArrow G A B
  /-- the leg is exactly the arrow's underlying link -/
  leg_eq : arrow.stripIso.toLink = leg

/-- S2/G1 conditional supply for a Kummer-type leg in the reverse (stored) direction
of Remark 3.10.2: the square stores the first vertical arrow from the lower strip to
the upper strip, and the leg walks the opposite way through the inverse
representative. -/
structure SourceReverseKummerLegUpgrade (G : Type uG) [Group G] [TopologicalSpace G]
    {A C : FPrimeStrip.{umon, uv, upi} V} (leg : FPrimeStripLink A C) where
  /-- the source Kummer arrow stored in the reverse direction -/
  arrow : Theorem311Source.SourceKummerArrow G C A
  /-- the leg is the underlying link of the inverse representative -/
  leg_eq : arrow.stripIso.symm.toLink = leg

/-! ## 3. The assembled SHE square supply (S2 + G1, conditional) -/

/-- The conditional Card-SHE supply: a link-level simultaneity square together with
per-leg upgrade records whose legs are definitionally the square's legs.  The
condition for producing one is an inhabitant of `SourceKummerEvaluationSquare`
(Section 4); producing one from gate-only arrow witnesses is not a construction of
the paper's arrows. -/
structure SourceSHESquareSupply (G : Type uG) [Group G] [TopologicalSpace G]
    (A B C D : FPrimeStrip.{umon, uv, upi} V) where
  upperHorizontalLeg : FPrimeStripLink A B
  lowerHorizontalLeg : FPrimeStripLink C D
  leftKummerLeg : FPrimeStripLink A C
  rightKummerLeg : FPrimeStripLink B D
  /-- the SHE link square whose legs are the four recorded legs -/
  square : SourceSimultaneousHolomorphicExpression A B C D
    upperHorizontalLeg lowerHorizontalLeg leftKummerLeg rightKummerLeg
  /-- the upper horizontal leg with its evaluation-arrow record -/
  upperHorizontalUpgrade : SourceEvaluationLegUpgrade G upperHorizontalLeg
  /-- the lower horizontal leg with its evaluation-arrow record -/
  lowerHorizontalUpgrade : SourceEvaluationLegUpgrade G lowerHorizontalLeg
  /-- the left Kummer leg with its reverse-direction Kummer-arrow record -/
  leftKummerUpgrade : SourceReverseKummerLegUpgrade G leftKummerLeg
  /-- the right Kummer leg with its reverse-direction Kummer-arrow record -/
  rightKummerUpgrade : SourceReverseKummerLegUpgrade G rightKummerLeg

namespace SourceSHESquareSupply

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A B C D : FPrimeStrip.{umon, uv, upi} V}

/-- The square's simultaneity field is evidence for its own (SHE) slot statement:
the consumer-facing form for `she := W.square.sheStatement` at the finite bridge
slot `FiniteStepXILinkEvidence.she` (FiniteCertificateBridge.lean). -/
theorem sheStatement_evidence (W : SourceSHESquareSupply G A B C D) :
    W.square.sheStatement :=
  W.square.simultaneous

/-- Evidence transport into a named `StepXIContract.she` field equated to the
square's statement (Contract.lean:38/:41). -/
theorem sheSlot_evidence (W : SourceSHESquareSupply G A B C D)
    {contract : StepXIContract} (h : contract.she = W.square.sheStatement) :
    contract.she :=
  W.square.sheSlot_evidence h

end SourceSHESquareSupply

/-! ## 4. The bridge from the Remark-3.10.2 square (S2 + G1, conditional) -/

namespace Theorem311Source
namespace SourceKummerEvaluationSquare

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A B C D : FPrimeStrip.{umon, uv, upi} V}

/-- The link-level SHE square induced by the reduced Remark-3.10.2 square: the two
composite expressions are read through `FPrimeStripEquiv.toLink` and the two-path
equality is the image of the recorded commutation. -/
def sheLinkSquare (S : SourceKummerEvaluationSquare G A B C D) :
    SourceSimultaneousHolomorphicExpression A B C D
      S.upperHorizontal.stripIso.toLink
      S.lowerHorizontal.stripIso.toLink
      (S.leftKummer.stripIso.symm).toLink
      (S.rightKummer.stripIso.symm).toLink where
  domainExpression := S.codomainExpression.toLink
  codomainExpression := S.domainExpression.toLink
  simultaneous := by rw [S.domainExpression_eq_codomainExpression]

/-- The assembled conditional supply: the SHE link square together with the four
per-leg upgrade records, all definitional from the source square's arrow records.
The condition is exactly the inhabitant `S` (and its source-grade faithfulness,
which is the recorded pending card, not a property of this construction). -/
def sheSupply (S : SourceKummerEvaluationSquare G A B C D) :
    SourceSHESquareSupply G A B C D where
  upperHorizontalLeg := S.upperHorizontal.stripIso.toLink
  lowerHorizontalLeg := S.lowerHorizontal.stripIso.toLink
  leftKummerLeg := (S.leftKummer.stripIso.symm).toLink
  rightKummerLeg := (S.rightKummer.stripIso.symm).toLink
  square := S.sheLinkSquare
  upperHorizontalUpgrade := ⟨S.upperHorizontal, rfl⟩
  lowerHorizontalUpgrade := ⟨S.lowerHorizontal, rfl⟩
  leftKummerUpgrade := ⟨S.leftKummer, rfl⟩
  rightKummerUpgrade := ⟨S.rightKummer, rfl⟩

end SourceKummerEvaluationSquare
end Theorem311Source

/-! ## 5. S3: the fixed one-column label binding -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- S3 new fact: every theater along the fixed column `1` carries the same
`InitialThetaArithmeticData` as the source -- the theater-family arithmetic data is
constant along the fixed one-column.  This is the column-binding step that
`SourceSharedBoundary.lean` did not record (its projections are the procession and
q/scale transport); the label "1,o" itself is not constructed. -/
theorem oneColumnTheater_arithmetic (m : Int) :
    (I.oneColumnTheater m).arithmetic = I.h1.source.arithmetic :=
  I.h1TheaterAt_arithmetic 1 m

/-- Corollary form: arithmetic data equality between any two column theaters. -/
theorem oneColumnTheater_arithmetic_constant (m m' : Int) :
    (I.oneColumnTheater m).arithmetic = (I.oneColumnTheater m').arithmetic :=
  (I.oneColumnTheater_arithmetic m).trans
    (I.oneColumnTheater_arithmetic m').symm

/-- The frozen S3 binding record: the proved fixed-one-column projections plus the
arithmetic-data constancy above, packaged as one supply.  Everything here is
discharged by the existing theorems; nothing about the 1,o ring/scheme layer is
claimed (tracked by `IUT-III.source-arithmetic-holomorphic-landing`). -/
structure SourceOneColumnLabelBinding where
  /-- the theater-family arithmetic data along the column -/
  theater_arithmetic : ∀ m : Int,
    (I.oneColumnTheater m).arithmetic = I.h1.source.arithmetic
  arithmetic_constant : ∀ m m' : Int,
    (I.oneColumnTheater m).arithmetic = (I.oneColumnTheater m').arithmetic
  /-- the F/D procession compatibility of the fixed column -/
  toD : ∀ k : Nat,
    (I.oneColumnFProcession.stage k).toD = (I.oneColumnDProcession.stage k)
  /-- injectivity of the top-stage source map -/
  source_injective : Function.Injective (I.oneColumnTopStage).source
  /-- cardinality of the fixed-column index set -/
  cardinality : Fintype.card (OneColumnIndex l) = lStar l.value + 1

/-- Constructor: the S3 binding, fully discharged by proved projections.  (The
record has only propositional fields, so it is stated as a theorem.) -/
theorem sourceOneColumnLabelBinding : SourceOneColumnLabelBinding I :=
  { theater_arithmetic := fun m => I.oneColumnTheater_arithmetic m
    arithmetic_constant := fun m m' => I.oneColumnTheater_arithmetic_constant m m'
    toD := fun k => I.oneColumnProcession_toD k
    source_injective := I.oneColumnTopStage_source_injective
    cardinality := oneColumnTopStage_cardinality }

end OriginalInput
end Theorem311Source

/-! ## 6. S4: the hull-expression readout supply -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- S4 conditional supply (value-level reduction): the readouts of the two SHE
composite expressions, with the explicit condition that both readouts equal the
theta-pilot image at procession `n` and label `j`.  Supplying this record is the
reduced form of "the output is expressible in the holomorphic hull"; the
actual identification of the composites' values with the theta-pilot image is the
open source input, and the nondegeneracy of the hull (compactness / log-volume) is
outside the record (see `literalHullInterface_impossible`). -/
structure SourceHullExpressionSupply (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) where
  /-- the value-level readout of the domain-side composite -/
  domainRead : I.ThetaPilotPoint v
  /-- the value-level readout of the codomain-side composite -/
  codomainRead : I.ThetaPilotPoint v
  /-- explicit condition: the domain-side readout is the theta-pilot image -/
  domainRead_eq : domainRead = I.sourceThetaPilotPoint v R n j
  /-- explicit condition: the codomain-side readout is the theta-pilot image -/
  codomainRead_eq : codomainRead = I.sourceThetaPilotPoint v R n j

namespace SourceHullExpressionSupply

variable {v : V} {R : I.SourceImageRealization v}
variable {n : ThetaPilotCarrier l} {j : SignedLabel l.value}

/-- The domain-side readout lies in the source holomorphic hull. -/
theorem domainRead_mem (W : SourceHullExpressionSupply I v R n j) :
    W.domainRead ∈ I.sourceHolomorphicHull v R n := by
  rw [W.domainRead_eq]
  exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j

/-- The codomain-side readout lies in the source holomorphic hull. -/
theorem codomainRead_mem (W : SourceHullExpressionSupply I v R n j) :
    W.codomainRead ∈ I.sourceHolomorphicHull v R n := by
  rw [W.codomainRead_eq]
  exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j

/-- Both readouts lie in the hull: the simultaneous hull-expressibility reading. -/
theorem bothReads_mem (W : SourceHullExpressionSupply I v R n j) :
    W.domainRead ∈ I.sourceHolomorphicHull v R n ∧
      W.codomainRead ∈ I.sourceHolomorphicHull v R n :=
  ⟨W.domainRead_mem, W.codomainRead_mem⟩

end SourceHullExpressionSupply

end OriginalInput
end Theorem311Source

end

/-! ## 7. Audit registration -/

namespace Audit

/-- Card-SHE transport-obligation layer: the S2/S3/S4/G1 conditional supplies of
`SourceSHETransportObligations.lean`. -/
def sourceSHETransportObligations : Obligation :=
  { id := "IUT-III.source-SHE-transport-obligations"
    source :=
      "IUT III, Remark 3.11.1, (iii) (SHE); Remark 3.10.2; Corollary 3.12, " ++
        "proof, Steps (xi-b), (xi-c); Remark 3.9.5, (i), (ii)"
    status := VerificationStatus.interface
    note :=
      "Conditional S2/S3/S4/G1 supplies for Card-SHE. Proved: " ++
        "FPrimeStripEquiv.toLink with pointwise laws (S2 base); the bridge " ++
        "sheLinkSquare/sheSupply from the reduced Remark-3.10.2 square " ++
        "SourceKummerEvaluationSquare to the link-level SHE square, with " ++
        "per-leg upgrade records carrying the x-mu unit layers (S2/G1); the " ++
        "fixed one-column label binding SourceOneColumnLabelBinding with the " ++
        "new arithmetic-data constancy along the column (S3); the " ++
        "hull-readout supply SourceHullExpressionSupply with hull membership " ++
        "(S4). NOT constructed: the Kummer-arrow weight record (only the unit " ++
        "layer is modeled); the 1,o ring/scheme layer (tracked by " ++
        "IUT-III.source-arithmetic-holomorphic-landing and its pending " ++
        "evidence card); source-grade inhabitants of the upgrade records " ++
        "(the Theorem-3.11 arrow records have gate witnesses only, per " ++
        "IUT-III.source-kummer-evaluation-arrows); the hull nondegeneracy " ++
        "(literalHullInterface_impossible). The G1 negative result " ++
        "(ProbeCardIPLG1Verdict.lean, SHA D660C2B4..., report section 15.3) " ++
        "is cited, not re-proved. No slot is closed by True."
    dependsOn :=
      [ "IUT-III.SHE",
        "IUT-III.source-SHE-simultaneity-exchange",
        "IUT-III.source-kummer-evaluation-arrows",
        "IUT-III.source-arithmetic-holomorphic-landing",
        "IUT-I-II.prime-strip-core" ] }

/-- Named card: an actual source inhabitant of `SourceSHESquareSupply` -- an
inhabitant of `SourceKummerEvaluationSquare` whose arrow records are the paper's
actual arrows (not gate witnesses), together with the weight records and the
compactness/log-volume nondegeneracy. -/
def sourceSHESquareSupply : Obligation :=
  { id := "IUT-III.source-SHE-square-supply"
    source := "IUT III, Remark 3.11.1, (iii) (SHE); Remark 3.10.2"
    status := VerificationStatus.pending
    note :=
      "Bridge availability: Theorem311Source.SourceKummerEvaluationSquare." ++
        "sheSupply (SourceSHETransportObligations.lean) turns an inhabitant " ++
        "into the link-level SHE square with unit-layer records. Consumers: " ++
        "StepXIContract.she/she_evidence (Contract.lean:38/:41) and the finite " ++
        "bridge slot FiniteStepXILinkEvidence.she/she_evidence " ++
        "(FiniteCertificateBridge.lean). The actual source inhabitant is not " ++
        "constructed; gate witnesses alone are excluded as SHE evidence."
    dependsOn := ["IUT-III.source-SHE-transport-obligations"] }

end Audit

end LeanFormal.IUT
