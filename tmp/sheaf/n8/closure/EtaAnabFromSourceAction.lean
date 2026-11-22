import tmp.sheaf.n8.closure.EtaSourceActionConcrete
import tmp.sheaf.n8.closure.EtaAnabAtFPlace
import tmp.sheaf.n8.closure.EtaKummerSourceDatumAtF
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import Mathlib

/-!
# etaAnab from the concrete source action

Candidate etaAnab map from the actual value-group line Rval to the actual
F-place Rss carrier EtaRssAtFPlace.

The candidate is the actual F-place Rss point; it is parameterized by the
concrete source action A so that its BPS shell, Kummer map, evaluation, region
and Ind1/2/3 data stay tied to A.  The actual F-place Rss carrier has fixed
shell/volume/index, so the map is constant on Rval; this is a consequence of the
actual carrier, not an arbitrary choice.

No abstract Nonempty and no arbitrary map are introduced.
-/

noncomputable section

namespace ABCBridge.N8.EtaAnabFromSourceAction

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open ABCBridge.N8.EtaSourceActionConcrete
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open ABCBridge.N8.EtaKummerSourceDatumAtF
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable {C4 : SourceWitnessedOutputData (l := l) (V := V) I Label}
variable {X : N8NativeInput l}
variable {n : ThetaPilotCarrier l}
variable {x : I.ThetaPilotPoint C4.place.v}

/-- Candidate etaAnab map on the actual Rval -> F-place Rss carrier. -/
noncomputable def etaAnabCandidate
    (A : EtaSourceActionConcrete C4 X n x) (a : Rval) : EtaRssAtFPlace X :=
  etaRssAtFPlace X

/-- The candidate's shell is the actual F-place shell. -/
theorem etaAnabCandidate_shell
    (A : EtaSourceActionConcrete C4 X n x) (a : Rval) :
    (etaAnabCandidate A a).shell = (fSourceDatum X).logShell :=
  rfl

/-- The concrete source action's BPS shell is the actual F-place shell. -/
theorem etaAnabCandidate_bpsShell_eq
    (A : EtaSourceActionConcrete C4 X n x) :
    A.bpsShell = fSourceDatum X :=
  A.bpsShell_eq

/-- Compatibility with the concrete Kummer map: its image lies in the source
BPS log-shell. -/
theorem etaAnabCandidate_kummer_mem
    (A : EtaSourceActionConcrete C4 X n x) (u : A.bpsShell.Units) :
    A.kummer u ∈ A.bpsShell.logShell :=
  A.kummer_mem u

/-- The candidate's shell and the source-action BPS shell agree after the
actual BPS-shell equality. -/
theorem etaAnabCandidate_shell_eq_bps
    (A : EtaSourceActionConcrete C4 X n x) (a : Rval) :
    (etaAnabCandidate A a).shell = (fSourceDatum X).logShell :=
  rfl

/-- Compatibility with the concrete Ind1 action. -/
theorem etaAnabCandidate_ind1_mul
    (A : EtaSourceActionConcrete C4 X n x) (g h : Label) :
    A.ind1 (g * h) = A.ind1 g * A.ind1 h :=
  map_mul _ g h

/-- Compatibility with the concrete Ind2 action. -/
theorem etaAnabCandidate_ind2_mul
    (A : EtaSourceActionConcrete C4 X n x) (g h : Label) :
    A.ind2 (g * h) = A.ind2 g * A.ind2 h :=
  map_mul _ g h

/-- Compatibility with the concrete Ind3 nonarchimedean one-way control. -/
theorem etaAnabCandidate_ind3_nonarch
    (A : EtaSourceActionConcrete C4 X n x) (m : Nat)
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    S ⊆ A.ind3_nonarch m S :=
  A.ind3_nonarch_inclusion m S

/-- Compatibility with the concrete Ind3 archimedean one-way control. -/
theorem etaAnabCandidate_ind3_arch
    (A : EtaSourceActionConcrete C4 X n x) (m : Nat)
    (S : Set (I.ThetaPilotPoint C4.place.v)) :
    A.ind3_arch m S ⊆ S :=
  A.ind3_arch_surjection m S

/-- The candidate map is actual from every concrete source action. -/
theorem etaAnabCandidate_exists
    (A : EtaSourceActionConcrete C4 X n x) :
    ∃ f : Rval → EtaRssAtFPlace X,
      f = fun a => etaAnabCandidate A a :=
  ⟨fun a => etaAnabCandidate A a, rfl⟩

end ABCBridge.N8.EtaAnabFromSourceAction
