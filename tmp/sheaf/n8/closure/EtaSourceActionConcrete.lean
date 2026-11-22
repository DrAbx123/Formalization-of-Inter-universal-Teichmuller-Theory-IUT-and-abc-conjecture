import tmp.sheaf.n8.closure.EtaKummerSourceDatumAtF
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import Mathlib

/-!
# ETA source action concrete

Concrete source action package:

  actual F-place BPS/log-shell shell (EtaKummerSourceDatumAtF.fSourceDatum)
    -> actual Kummer map on the F shell units
    -> actual source theta evaluation and region (SourceWitnessedOutputData)
    -> actual Ind1/Ind2 region actions and Ind3 one-way controls.

Every field is tied to actual X / C4 / F-place shell data.  There is no abstract
Nonempty VerticalLogKummerCorrespondence and no Fmod shell.
-/

noncomputable section

namespace ABCBridge.N8.EtaSourceActionConcrete

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open ABCBridge.N8.EtaKummerSourceDatumAtF
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui uL u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I Label)
variable {X : N8NativeInput l}
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint C4.place.v)

/-- Concrete BPS -> Kummer -> evaluation -> region action package with actual
F-place shell content. -/
structure EtaSourceActionConcrete (X : N8NativeInput l) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v) where
  /-- BPS/log-shell datum from the actual F-place shell. -/
  bpsShell : SourceLogShellDatum
  bpsShell_eq : bpsShell = fSourceDatum X
  /-- Actual Kummer map on BPS units. -/
  kummer : bpsShell.Units → bpsShell.K
  kummer_eq : kummer = fun u => (bpsShell.logMap u).toAdd
  /-- Actual Kummer image membership in the BPS log-shell. -/
  kummer_mem : ∀ u : bpsShell.Units, kummer u ∈ bpsShell.logShell
  /-- Actual source theta evaluation. -/
  eval : C4.Choice n x → I.ThetaPilotPoint C4.place.v
  eval_eq : eval = C4.eval n x
  /-- Actual source region. -/
  region : Set (I.ThetaPilotPoint C4.place.v)
  region_eq : region = C4.U n x
  /-- Actual Ind1 action on the source carrier. -/
  ind1 : Label →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)
  ind1_eq : ind1 = C4.ind.ind1
  /-- Actual Ind2 action on the source carrier. -/
  ind2 : Label →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)
  ind2_eq : ind2 = C4.ind.ind2
  /-- Actual Ind3 one-way controls. -/
  ind3_nonarch : Nat → Set (I.ThetaPilotPoint C4.place.v) →
    Set (I.ThetaPilotPoint C4.place.v)
  ind3_nonarch_eq : ind3_nonarch = C4.ind.ind3_nonarch
  ind3_arch : Nat → Set (I.ThetaPilotPoint C4.place.v) →
    Set (I.ThetaPilotPoint C4.place.v)
  ind3_arch_eq : ind3_arch = C4.ind.ind3_arch
  ind3_nonarch_inclusion : ∀ n S, S ⊆ ind3_nonarch n S
  ind3_arch_surjection : ∀ n S, ind3_arch n S ⊆ S

/-- Actual concrete package: every component is the production C4/F-shell one. -/
def etaSourceActionConcrete : EtaSourceActionConcrete C4 X n x where
  bpsShell := fSourceDatum X
  bpsShell_eq := rfl
  kummer := fun u => ((fSourceDatum X).logMap u).toAdd
  kummer_eq := rfl
  kummer_mem := fun u => (fSourceDatum_codomainKummerContained X) ⟨u, rfl⟩
  eval := C4.eval n x
  eval_eq := rfl
  region := C4.U n x
  region_eq := rfl
  ind1 := C4.ind.ind1
  ind1_eq := rfl
  ind2 := C4.ind.ind2
  ind2_eq := rfl
  ind3_nonarch := C4.ind.ind3_nonarch
  ind3_nonarch_eq := rfl
  ind3_arch := C4.ind.ind3_arch
  ind3_arch_eq := rfl
  ind3_nonarch_inclusion := C4.ind.ind3_nonarch_inclusion
  ind3_arch_surjection := C4.ind.ind3_arch_surjection

/-- Actual Ind1 action law. -/
theorem etaSourceActionConcrete_ind1_mul (g h : Label) :
    (etaSourceActionConcrete (X := X) C4 n x).ind1 (g * h) =
      (etaSourceActionConcrete (X := X) C4 n x).ind1 g *
        (etaSourceActionConcrete (X := X) C4 n x).ind1 h :=
  map_mul _ g h

/-- Actual Ind2 action law. -/
theorem etaSourceActionConcrete_ind2_mul (g h : Label) :
    (etaSourceActionConcrete (X := X) C4 n x).ind2 (g * h) =
      (etaSourceActionConcrete (X := X) C4 n x).ind2 g *
        (etaSourceActionConcrete (X := X) C4 n x).ind2 h :=
  map_mul _ g h

/-- Actual Ind3 nonarchimedean one-way inclusion. -/
theorem etaSourceActionConcrete_ind3_nonarch
    (m : Nat) (S : Set (I.ThetaPilotPoint C4.place.v)) :
    S ⊆ (etaSourceActionConcrete (X := X) C4 n x).ind3_nonarch m S :=
  (etaSourceActionConcrete (X := X) C4 n x).ind3_nonarch_inclusion m S

/-- Actual Ind3 archimedean one-way surjection. -/
theorem etaSourceActionConcrete_ind3_arch
    (m : Nat) (S : Set (I.ThetaPilotPoint C4.place.v)) :
    (etaSourceActionConcrete (X := X) C4 n x).ind3_arch m S ⊆ S :=
  (etaSourceActionConcrete (X := X) C4 n x).ind3_arch_surjection m S

end ABCBridge.N8.EtaSourceActionConcrete
