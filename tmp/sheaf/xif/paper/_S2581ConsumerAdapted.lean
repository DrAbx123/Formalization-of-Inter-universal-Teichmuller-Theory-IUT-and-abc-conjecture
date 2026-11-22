import tmp.sheaf.xif.paper.S2581PrimitiveThetaActual

namespace ConsumerCheck

open LeanFormal.IUT.XiFPaper.S2581PrimitiveThetaActual
open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual

example : S2579Primitive := S2581_primitive
#check @S2581_primitive
#check @S2581_prime613_of_conductor_linear
#print axioms S2581_primitive
#print axioms S2581_prime613_of_conductor_linear

end ConsumerCheck
