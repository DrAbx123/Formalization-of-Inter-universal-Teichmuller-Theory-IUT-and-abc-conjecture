# S2460: actual constant pseudofunctor diagram; involution map blocked on dependent object reduction

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL: S2460Diagram : SignActionIndex ->p EtaleStackPseudofunctor F using
CategoryTheory.pseudofunctorOfIsLocallyDiscrete with
obj _ = S2482Orbicurve.stack.fiber, map _ = identity strong trans, mapId = refl,
mapComp = right-unitor inverse. This is a genuine pseudofunctor but its generator map is the IDENTITY, not S2482EllipticInvolution; it is NOT the required sign action and does not give cF.

EXIT=0, olean 38840, SHA256 e30eda16efefde72daf0c1528187671af5b671262a0308c0b9a660d96b5c07e1, axioms propext/Classical.choice/Quot.sound.

INVOLUTION MAP BLOCKER: S2461 attempt defines map f = if (f.as : SignGroup)=1 then id else S2482EllipticInvolution.
Because b b' : LocallyDiscrete (SingleObj SignGroup) are arbitrary objects, f.as has type b.as ⟶ b'.as and does not reduce to SignGroup/numerals without eliminating b,b'. First attempt produced synthInstanceFailed OfNat (b.as ⟶ b'.as) 1 and Decidable (f.as = 1). Need to eliminate b,b' (obtain LocallyDiscrete.mk, then cases on SingleObj) or use SingleObj.id_as_one/comp_as_mul to write the branches. mapId/mapComp then need group cases in SignGroup = Multiplicative (ZMod 2).

inversionSquared is available (S2459InvolutionSquared), so only the object-elimination/group-case engineering remains for the map/mapComp. No cF, no fake, no IsStack.