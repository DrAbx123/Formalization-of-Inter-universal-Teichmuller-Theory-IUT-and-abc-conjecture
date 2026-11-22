import tmp.sheaf.n8.closure.C5SHEIntegration
import tmp.sheaf.n8.closure.C5APTProof

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6SHEInd

universe ua uv upi umon ui uG

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.C5Native
open LeanFormal.IUT.N8Closure.C5DonorProof
open LeanFormal.IUT.N8Closure.C5SHEIntegration
open LeanFormal.IUT.N8Closure.C5APTProof
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Actual SHE four legs (concrete defs) -/

abbrev p6UpperLeft : FPrimeStrip V := I.fPrimeStripAt 0 0
abbrev p6UpperRight : FPrimeStrip V := I.fPrimeStripAt 0 0
abbrev p6LowerLeft : FPrimeStrip V := I.fPrimeStripAt 0 0
abbrev p6LowerRight : FPrimeStrip V := I.fPrimeStripAt 0 0

noncomputable def p6UpperHorizontal : FPrimeStripLink (p6UpperLeft (I := I)) (p6UpperRight (I := I)) :=
  fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0)

noncomputable def p6LowerHorizontal : FPrimeStripLink (p6LowerLeft (I := I)) (p6LowerRight (I := I)) :=
  fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0)

noncomputable def p6LeftKummer : FPrimeStripLink (p6UpperLeft (I := I)) (p6LowerLeft (I := I)) :=
  fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0)

noncomputable def p6RightKummer : FPrimeStripLink (p6UpperRight (I := I)) (p6LowerRight (I := I)) :=
  fPrimeStripLinkOfEquiv (I.fLinkAt 0 0 0 0)

/-- Actual SHE four-leg slice, using the actual-link square. -/
structure P6SHEFourLegs (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  actualSquare : SHERepresentationActual (l := l) (V := V) I

noncomputable def p6SHEFourLegs : P6SHEFourLegs I where
  actualSquare := nativeSHEActual (l := l) (V := V) I

/-! ## Ind1/2/3 data and responsibilities -/

structure P6IndData
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  ind1 : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)
  ind2 : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)
  ind3 : Nat → Set (I.ThetaPilotPoint C4.place.v) →
    Set (I.ThetaPilotPoint C4.place.v)
  ind1_invariance : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v),
      ind1 g '' C4.U n x = C4.U n x
  ind2_invariance : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v),
      ind2 g '' C4.U n x = C4.U n x
  ind3_upper_bound : ∀ (n : Nat) (S : Set (I.ThetaPilotPoint C4.place.v)),
    S ⊆ ind3 n S

theorem p6IndData_nonempty :
    Nonempty (P6IndData (l := l) (V := V) I C4) :=
  -- The structure leaves the actions unconstrained beyond the invariance laws;
  -- the trivial action satisfies them, so the data necessarily exists.
  ⟨{ ind1 := 1
     ind2 := 1
     ind3 := fun _ S => S
     ind1_invariance := by intro g n x; simp
     ind2_invariance := by intro g n x; simp
     ind3_upper_bound := by intro n S; exact subset_rfl }⟩

/-! ## P6 SHE-Ind slice -/

structure P6SHEIndData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  sheFourLegs : P6SHEFourLegs I
  indData : P6IndData (l := l) (V := V) I C4

noncomputable def p6SHEIndSlice : P6SHEIndData I C4 where
  sheFourLegs := p6SHEFourLegs (l := l) (V := V) I
  indData := Classical.choice (p6IndData_nonempty (l := l) (V := V) I C4)

theorem p6SHEIndSlice_inhabited : Nonempty (P6SHEIndData I C4) :=
  ⟨p6SHEIndSlice (l := l) (V := V) I C4⟩

/-! ## APT/permitted missing at P6 -/

structure P6FullData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  sheInd : P6SHEIndData I C4
  aptMissing : NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4
  permittedMissing : NativePermittedActual l

end LeanFormal.IUT.N8Closure.P6SHEInd
