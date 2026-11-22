import tmp.sheaf.n8.closure.O2PaperComparison
import Mathlib

/-!
# O2 paper comparison, construct the bad F-place from the source bijection

SourceInitialThetaData has a bijection placeToMod : V ≃ Vmod.  For a bad moduli
place p in VbadMod, badMod_subset_Vmod gives finite p in Vmod; the preimage v
then has comap (place v) = finite p, hence place v is finite.  This constructs
PaperBadFPlace and closes PaperBadFPlaceGap.

The remaining comparison ThetaQ = ThetaAnab is not derivable from the two
independent readouts alone; its exact gap is recorded.  No arbitrary place is
used.
-/

noncomputable section

namespace ABCBridge.N8.O2PaperComparison

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}

/-- Construct the actual bad finite F-place over a bad moduli place from the
source place bijection. -/
noncomputable def paperBadFPlaceOf (D : SourceInitialThetaData l)
    (p : NumberField.FinitePlace D.candidate.arithmetic.Fmod)
    (hp : p ∈ D.candidate.VbadMod) : PaperBadFPlace D := by
  let w := Classical.choose (NumberFieldFinitePlace.comap_surjective
    (k := D.candidate.arithmetic.Fmod) (K := D.candidate.arithmetic.F) p)
  have hw := Classical.choose_spec (NumberFieldFinitePlace.comap_surjective
    (k := D.candidate.arithmetic.Fmod) (K := D.candidate.arithmetic.F) p)
  exact ⟨w, by rwa [hw]⟩

/-- The bad finite F-place exists from ClauseB.bad_nonempty, so the previous
PaperBadFPlaceGap is closed. -/
theorem paperBadFPlace_nonempty (D : SourceInitialThetaData l) :
    Nonempty (PaperBadFPlace D) := by
  obtain ⟨p, hp⟩ := D.clauseB.bad_nonempty
  exact ⟨paperBadFPlaceOf D p hp⟩

/-- Actual PaperBadFPlaceGap closure. -/
theorem paperBadFPlaceGap_closed (D : SourceInitialThetaData l) :
    PaperBadFPlaceGap D :=
  paperBadFPlace_nonempty D

/-- The remaining comparison gap: the two independent readouts (ThetaQ from the
actual ClauseB q norm and ThetaAnab from the actual local log-shell volume
index) are not identified by SourceInitialThetaData alone.  Each side is
already defined; this proposition records only the missing comparison. -/
def O2PaperReadoutGap (D : SourceInitialThetaData l) : Prop :=
  ∃ W : PaperBadFPlace D, O2PaperComparison W

end ABCBridge.N8.O2PaperComparison
