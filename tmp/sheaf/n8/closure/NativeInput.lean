import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamily

/-!
# N8 native input slice

New C0/C1 input root: actual native initial Theta data, with the
Definition 3.1(e) place section and a dependent theater/log-theta lattice.
No arbitrary external V and no old selected realization are inputs.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.NativeInput

open LeanFormal.IUT

universe u ua uv upi umon ui

/-- The actual Definition 3.1(e) place subtype selected by the native data. -/
abbrev NativePlaces (S : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData l) :=
  { v : NumberFieldPlace S.arithmetic.K // v ∈ S.tuple.source.V }

/-- Native place bijection: selected places are exactly the base places. -/
noncomputable def nativePlaceEquiv (S : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData l) :
    NativePlaces S ≃ NumberFieldPlace S.arithmetic.Fmod :=
  S.tuple.source.V_mod_bijection.symm

theorem nativePlaceEquiv_comap (S : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData l)
    (v : NativePlaces S) :
    NumberFieldPlace.comap (k := S.arithmetic.Fmod) v.1 =
      nativePlaceEquiv S v :=
  S.tuple.source.V_place_comap v

/-- The dependent lattice over native places; arithmetic alignment is supplied. -/
structure NativeLattice (S : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData l) where
  family : LeanFormal.IUT.SourceHodgeTheaterFamily l (NativePlaces S)
  arithmetic_alignment : ∀ i, (family.theater i).arithmetic = S.arithmetic

/-- New C0 input: native initial Theta data plus its actual lattice. -/
structure N8NativeInput (l : PrimeGeFive) where
  S : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData l
  lattice : NativeLattice S

namespace N8NativeInput

variable {l : PrimeGeFive} (X : N8NativeInput l)

abbrev places := NativePlaces X.S

noncomputable def placeEquiv : places X ≃ NumberFieldPlace X.S.arithmetic.Fmod :=
  nativePlaceEquiv X.S

theorem placeEquiv_comap (v : places X) :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1 = placeEquiv X v :=
  nativePlaceEquiv_comap X.S v

abbrev family : LeanFormal.IUT.SourceHodgeTheaterFamily l (places X) :=
  X.lattice.family

theorem arithmetic_at (i : X.family.index) :
    (X.family.theater i).arithmetic = X.S.arithmetic :=
  X.lattice.arithmetic_alignment i

end N8NativeInput

end LeanFormal.IUT.N8Closure.NativeInput