import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
noncomputable section
namespace Probe
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable (k : Type) [Field k] [NumberField k] (v : NumberField.FinitePlace k)
#check (algebraMap (NumberField.RingOfIntegers k) (CompletionIntegers v) : NumberField.RingOfIntegers k → CompletionIntegers v)
#check (algebraMap k (Completion v) : k → Completion v)
#check (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers v.maximalIdeal.asIdeal (Completion v))
end Probe
