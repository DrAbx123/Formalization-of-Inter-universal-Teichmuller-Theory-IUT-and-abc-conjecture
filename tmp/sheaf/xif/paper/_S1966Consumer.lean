import tmp.sheaf.xif.paper.S1966LocalThetaMonoidActual

set_option linter.unusedVariables false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1966LocalThetaMonoidActual

namespace S1966Consumer

#check thetaToGaussian_bijective
#check packetGaussianValueMonoid
#check packetEvaluation_bijective
#check gaussianFivePacket_evaluation_injective
#check LocalThetaMonoidModel
#check localGaussianValueMonoid
#check localEvaluation_bijective
#check localEvaluation_generator
#check localEvaluation_units
#check hodgePacketGaussianValueMonoid

example (l : PrimeGeFive) (p : Nat) (hp : Nat.Prime p) :
    Function.Bijective (thetaToGaussian p l) :=
  thetaToGaussian_bijective p hp l

example (l : PrimeGeFive) :
    Function.Injective (packetEvaluation (gaussianFivePacket l)) :=
  gaussianFivePacket_evaluation_injective

example (v : FinitePrimePlace 2 7) (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    Function.Bijective (localEvaluation v p l) :=
  localEvaluation_bijective v p hp l

example (v : FinitePrimePlace 2 7) (p : Nat) (hp : Nat.Prime p) (l : PrimeGeFive) :
    (fun j => (1, Multiplicative.ofAdd (gaussianNNWeight p l j))) ∈
      localGaussianCarrier v p l :=
  by simpa using localGaussian_mem v p l 1

end S1966Consumer
