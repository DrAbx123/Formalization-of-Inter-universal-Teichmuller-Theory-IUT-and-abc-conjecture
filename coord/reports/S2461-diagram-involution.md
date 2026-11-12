# S2461: involution diagram progress — map/mapComp compile except unitor inference

Date: 2026-11-02. Serialized lake env lean -j1.

Using LocallyDiscrete.mkPseudofunctor (source B0 = SingleObj SignGroup) instead of pseudofunctorOfIsLocallyDiscrete avoids the b.as projection problem.

Current S2461 source:
- map via cases b/b'/lets f' : SignGroup := f, if f'=1 then id else S2482EllipticInvolution;
- mapId compiles;
- mapComp branches compile structurally (id,id)/(id,g)/(g,id)/(g,g) with SingleObj.comp_as_mul/hh/S2461_mul_eq_one and S2459InvolutionSquared.symm;
- ONLY remaining errors: Bicategory.leftUnitor/rightUnitor cannot infer the bicategory of Xf in the mixed branches:
  Application type mismatch: S2482EllipticInvolution has type S2482Orbicurve.Hom but expected ?m ⟶ ?m, in λ_/ρ_.
  Need to provide the Bicategory instance/object type explicitly, e.g. show the hom as a 1-morphism in EtaleStackPseudofunctor F with open scoped Pseudofunctor.StrongTrans Bicategory, or use the strict/eqToHom unitors.

No actual diagram yet; no cF/cK. No fake.