import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

open LeanFormal.IUT

universe u v w

#check LocalAbsoluteGalois
#check (inferInstance : Group (LocalAbsoluteGalois 5))
#check (inferInstance : TopologicalSpace (LocalAbsoluteGalois 5))
#check (inferInstance : CommGroup ((AlgebraicClosure ℚ_[5])ˣ))
#check FPrimeStrip
#check FPrimeStrip.{0,0,0}
#check localFPrimeStrip
#check (localFPrimeStrip.toDPrimeStrip.Pi (⟨5, by norm_num⟩ : RationalPrimePlace))
#check (inferInstance : Group (localFPrimeStrip.toDPrimeStrip.Pi (⟨5, by norm_num⟩ : RationalPrimePlace)))
#check (inferInstance : TopologicalSpace (localFPrimeStrip.toDPrimeStrip.Pi (⟨5, by norm_num⟩ : RationalPrimePlace)))
#check TimesMuKummer.Ism
#check TimesMuKummer.Ism (localFPrimeStrip.action (⟨5, by norm_num⟩ : RationalPrimePlace))
#check (inferInstance : Group (TimesMuKummer.Ism (localFPrimeStrip.action (⟨5, by norm_num⟩ : RationalPrimePlace))))
#check MonoidAlgebra.domCongrAut
#check SourceLogShellDatum
#check SourceLogShellDatum.IQSpan
#check sourceLocalLogShellDatum
#check (inferInstance : TopologicalSpace (localFPrimeStrip.toDPrimeStrip.Pi (⟨5, by norm_num⟩ : RationalPrimePlace)))
