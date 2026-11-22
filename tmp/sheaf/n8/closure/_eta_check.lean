import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellVolumeConsumer
open scoped Padic
example : Fact (Nat.Prime (5:PrimeGeFive).value) := inferInstance
#check integralLogShell
#check logShellVolumeConsumer
#check LeanFormal.IUT.Foundations.LocalFields.LogShellVolume.logShellVolumeConsumer
#check LeanFormal.IUT.IntegralLogShell
