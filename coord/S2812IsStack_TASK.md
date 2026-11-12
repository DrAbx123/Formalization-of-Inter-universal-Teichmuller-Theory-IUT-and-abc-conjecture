# IsStack for schemeRepresentableEtalePseudofunctor

Lean 4.32.2 + Mathlib v4.32.2, D:/lean.

## Inputs (ACTUAL)
- tmp/sheaf/xif/paper/S2811P6PrestackActual.lean:
  presheafHom_obj_eq, presheafHom_subsingleton, presheafHomIso,
  P_isSheaf, presheafHom_isSheaf,
  instance schemeRepresentableEtalePseudofunctor_isPrestack.
- tmp/sheaf/xif/paper/S2811IsPrestackActual.lean:
  S2811_yoneda_isSheaf, schemeOverFieldEtaleTopologySubcanonical.
- Iut/Foundations/Orbicurve.lean: schemeRepresentableEtalePseudofunctor.

## Goal
instance (F) [Field F] (X : SchemeOverField F) :
  (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
    (Iut.SchemeOverField.etaleTopology F)

Use Pseudofunctor.IsStack.of_isStackFor (Mathlib/CategoryTheory/Sites/Descent/IsStack.lean:77).
For every object S and covering sieve R, prove IsStackFor R.arrows for Fiber.
Descent data objects are morphisms U -> X; use sheaf/separatedness of yoneda.obj X
(S2811_yoneda_isSheaf) to glue compatible families and prove uniqueness/effectiveness.

Compile:
lake env lean -j1 -R 'D:/lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2812IsStackActual.olean tmp/sheaf/xif/paper/S2812IsStackActual.lean
Report EXIT, first error, src/olean SHA, axioms. No sorry/extra axioms.