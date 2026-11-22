import tmp.sheaf.xif.paper.S3139SourceBPSActual
import tmp.sheaf.xif.paper.S3139SourceEtHTActual
import tmp.sheaf.xif.paper.S3138SourceStepXIActual
import tmp.sheaf.xif.paper.S3134FourthJointCompositeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: Stage-1 seams (BPS / etHT to the S3134 and S3138 consumers)

Stage-1 named objects are built in `S3139SourceBPSActual` (BPS, Theta-link
gluing data) and `S3139SourceEtHTActual` (vertically coric etale Hodge
theater).  This file records the seams to the fourth-triangle consumer of
S3134 (the `(hull+det) circ (dsc)` composite, source IUT III, Corollary 3.12,
Steps (xi-d)-(xi-f)) and to the source-level Step XI boundary of S3138.

Paper source: Formalization of IUT (2026-04), §4 :443-546 (the four triangles:
BPS --mlt algo--> mlt rep --hull+det--> ...; BPS+0-col --forget--> BPS+etHT
--(SHE)--> q-plt.+etHT), and :602-621 (stage split: Thm 3.11 = (dsc)+APT+IPL,
Thm 3.11.5 = (hull+det) circ (dsc) + SHE+IPL, Cor 3.12 = comparison).

What is actual here (no arbitrary data):

* `sourceBPS_stepXIInput_underlying`: the BPS at `(n,m)` has the same
  underlying F-prime-strip as the theater of the S3138 source Step XI input;
  the etHT at `(n,m)` has the same domain theater; both are rfl projections;
* `S3134StageOneSupply`: the exact supply record of the fourth triangle.  Its
  parameters are actual objects (BPS, etHT) and its fields are the actual S3134
  consumer records (`S1300HDDHullDetSource`, `SourceSHEHDDCompatibility`)
  together with the concrete named paper hypotheses (Theta-pilot gluing and
  0-column association); from them the actual S3134 composite readout and its
  nonempty hull lattice are produced;
* `SourceMultiradialMutationDemand`: the exact missing first-triangle mutation
  BPS -> mlt rep (:505-513), recorded as a demand structure with the actual
  endpoints; it has no inhabitant in the tree and is not claimed.

No sorry, axiom, True, PUnit, arbitrary carrier, or toy data.
-/

namespace LeanFormal.IUT.XiFPaper.S3139StageOneSeamsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3139SourceBPSActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual
open LeanFormal.IUT.XiFPaper.S3139SourceEtHTActual.SourceEtHT
open LeanFormal.IUT.XiFPaper.S3138SourceStepXIActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCarrierActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual

universe u v ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-! ## 1. The S3138 seam: BPS / etHT versus the source Step XI input -/

/-- The BPS of the theater of the source Step XI input at `(n,m)` has the same
underlying prime strip as that theater. -/
theorem sourceBPS_stepXIInput_underlying
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceBPSOfTheater J n m).underlying =
      (sourceStepXIInput J n m).theater.primeStrip := rfl

/-- The actual times-mu gluing between the BPS at `(n,m)` and the canonical
times-mu strip of the S3138 theater strip (reflexive full poly-isomorphism). -/
def sourceBPS_stepXIStepGluing
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    SourceFTimesMuPrimeStripEquivalence (sourceBPSOfTheater J n m).timesMuStrip
      (SourceFTimesMuPrimeStrip.canonical
        (sourceStepXIInput J n m).theater.primeStrip) :=
  SourceFTimesMuPrimeStripEquivalence.refl _

/-- The etHT at `(n,m)` (same domain and codomain) has the domain theater of
the S3138 source Step XI input. -/
theorem sourceEtHT_stepXIInput_domain
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceEtHTAt J n m n m).domain = (sourceStepXIInput J n m).theater := rfl

/-! ## 2. The fourth-triangle supply record (exact seam) -/

/-- The exact supply record of the fourth triangle `(hull+det) circ (dsc)`.
The BPS and the etHT are parameters (actual Stage-1 objects); the fields are
the actual S3134 consumer records and the concrete named hypotheses
(Formalization :497-524). -/
structure S3134StageOneSupply
    (I31 : Input Label Choice) (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (bps : SourceBPS V) (etHT : SourceEtHT l V) where
  /-- the actual hull+det source of the fourth triangle -/
  hdd : S1300HDDHullDetSource I31
  /-- the actual SHE/HDD compatibility record of the fourth triangle -/
  she : SourceSHEHDDCompatibility (I := I31) (J := J)
  /-- named hypothesis (Formalization :507-513): the BPS is glued by a full
  poly-isomorphism to the underlying BPS of the Theta-pilot at (0,0) -/
  bps_thetaPilot_glue :
    Nonempty (SourceFTimesMuPrimeStripEquivalence bps.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip)
  /-- named hypothesis (Formalization :520-524): the etHT is the 0-column etHT -/
  etHT_zero_column : etHT = sourceEtHTZeroColumn J 0

/-- Canonical supply: the constructible fields are constructed from the actual
original input; the two named paper hypotheses are discharged reflexively by
the canonical BPS/etHT choices.  The only genuinely supplied data are the
actual S3134 records `hdd`/`she`. -/
def S3134StageOneSupplyCanonical
    (I31 : Input Label Choice) (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (hdd : S1300HDDHullDetSource I31)
    (she : SourceSHEHDDCompatibility (I := I31) (J := J)) :
    S3134StageOneSupply I31 J (sourceBPSOfTheater J 0 0)
      (sourceEtHTZeroColumn J 0) where
  hdd := hdd
  she := she
  bps_thetaPilot_glue := ⟨SourceFTimesMuPrimeStripEquivalence.refl _⟩
  etHT_zero_column := rfl

namespace S3134StageOneSupply

variable {I31 : Input Label Choice} {J : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {bps : SourceBPS V} {etHT : SourceEtHT l V}
variable (S : S3134StageOneSupply I31 J bps etHT)

/-- The actual fourth-triangle composite `(hull+det) circ (dsc)` readout at a
place, from the supply. -/
def composite (v : NumberField.FinitePlace ℚ) :=
  S3134FourthJointComposite I31 J S.hdd S.she v

theorem composite_fst (v : NumberField.FinitePlace ℚ) :
    (S.composite v).1 =
      S3134SHEReadout (I := I31) (J := J) S.she v
        (S3134SHEOutputObject (I := I31)) := rfl

theorem composite_snd_nonempty (v : NumberField.FinitePlace ℚ) :
    (S.composite v).2.Nonempty :=
  S3134HullDetReadout_nonempty I31 S.hdd (S3134SHEOutputObject I31) v

end S3134StageOneSupply

/-! ## 3. Exact Missing: the first-triangle multiradial mutation -/

/-- The exact missing first-triangle mutation BPS -> mlt rep
(Formalization :505-513, :602-610; audit gap 2): a candidate algorithm map from
the Theta-pilot-glued BPS into the etHT radial target.  The BPS and the etHT are
parameters (actual endpoints); the mutation field is the demanded algorithm
map.  Its existence and the (Ind1)/(Ind2)/(Ind3) compatibility laws are the
demand; no inhabitant exists in the tree and none is claimed. -/
structure SourceMultiradialMutationDemand
    (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (bps : SourceBPS V) (etHT : SourceEtHT l V) where
  bps_glued :
    Nonempty (SourceFTimesMuPrimeStripEquivalence bps.timesMuStrip
      (sourceBPSOfTheater J 0 0).timesMuStrip)
  etHT_zero_column : etHT = sourceEtHTZeroColumn J 0
  /-- the candidate algorithm map read on the etale-like portions -/
  mutation : (v : V) → bps.etaleLikePortion v → etHT.etaleLikePortion v

end LeanFormal.IUT.XiFPaper.S3139StageOneSeamsActual

end
