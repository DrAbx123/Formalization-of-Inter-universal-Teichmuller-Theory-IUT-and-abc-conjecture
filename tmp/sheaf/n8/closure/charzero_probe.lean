import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open IsDedekindDomain
open scoped NumberField
variable {F : Type} [Field F] [NumberField F]
example (v : HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) := inferInstance
example (w : NumberField.InfinitePlace F) : CharZero (w.Completion) := inferInstance