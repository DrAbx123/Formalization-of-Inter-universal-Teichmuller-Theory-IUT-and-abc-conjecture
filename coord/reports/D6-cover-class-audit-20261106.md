# D6 cover-class audit (2026-11-06)

## Question

Is the actual paper D6 cover family the S2517 family (S2482/Qi model) or the S1726 arbitrary/weak cover type?

## Sources

| Source | Content |
|---|---|
| S1726OrbicurveFPrimeActual.lean | Actual D6 hyperbolic orbicurve over F' = SplittingField(S1687H*(X^2+1)); actual finite etale cover: split degree-two cover R' (x)_{F'} (F' x F') -> R'; header says the paper's connected cover and connectedness are not constructed. |
| S1728CoverCategoryActual.lean | S1728Cover = Iut.OrbicurveFiniteEtaleCover S1726Orbicurve; the formal weak cover category over the S1726 orbicurve. |
| S1850RefuteS1756Actual.lean | Doubled presentation is a legal S1728Cover but not coherent; S1852NotFirstMissing refutes coherence for all S1728Cover. |
| S1852CoherentCoverActual.lean | StrongCover/CoherentCover; terminal cover coherent; general S1728Cover not. |
| S2517InvObjActual.lean | S2517InvObj C is an actual finite-etale cover of S2482Orbicurve over F = S2480QiActual.F = Q(i), used for the inverse functor S2517InvFunctorPartial. |
| S2628CoherentConstructionActual.lean | For every C : FiniteEtaleCover S2482AffineScheme, S2517InvObj C is a StrongCover of S2482Orbicurve (via S2561 lift uniqueness + coneEssSurj bridge). |

## Audit conclusion

1. The actual paper D6 cover is the split degree-two cover over the S1726/F' orbicurve, not the arbitrary weak S1728Cover type.
2. The S2517 family is a concrete family of covers of the Qi(i)/S2482 model, not the S1726/F' split cover. It is used for the inverse-functor construction, and its base field is different.
3. S2628 therefore constructs actual StrongCover data for the S2517 model family, but it does NOT by itself close the paper D6 cover coherence.
4. The weak S1728Cover type also contains non-paper S1850 doubled presentations; coherence for all S1728Cover is false (S1852NotFirstMissing).
5. To close D6 actual, construct the S1726 split cover as an OrbicurveFiniteEtaleCover S1726Orbicurve and prove its coherence (StrongCover/CoherentCover) directly from the split algebra R' (x)_{F'} (F' x F'), or prove a model equivalence S2482/S1726 that transports S2517 strong data.

## Consequences for current interfaces

| Interface | Effect |
|---|---|
| S2628 s2517StrongCover | ACTUAL for S2482/Qi family; not the S1726/F' paper cover. |
| S2629 generic cancellation fields | ACTUAL; can consume S2482 StrongCover only if cancellation fields are provided; StrongCover alone does not supply them. |
| S2621/S2623 D6 chain | Still needs the paper cover's coherence/cancellation data; cannot be fed by S2517 model data without transport. |

## Next actual construction target

| Target | Required data |
|---|---|
| S1726 split cover object | OrbicurveFiniteEtaleCover S1726Orbicurve with source the split finite-etale algebra cover and map to S1726Orbicurve.stack |
| StrongCover for it | StrongEtaleStackFiniteEtaleMorphism with coneEssSurj at every base change, using the explicit splitting F' x F' |
| CoherentCover for it | StrongCover + S1756Unit, derived from the same splitting |

No fake witness is asserted.
