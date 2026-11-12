# S1946: the F'-algebra chart identification Away WGr Zbar ≃ₐ[F'] R' is constructed

Date: 2026-11-01.  Task: fill the *first missing* datum of S1937, the F'-algebra chart
identification

    S1937ChartAlgEquiv : (Away WGr Zbar) ≃ₐ[S1726K] S1726CoordinateRing

by the S1937 recipe (psi : R' -> Away, x |-> X/Z, y |-> Y/Z; phi : Away -> R' by
dehomogenization at Z; the homogeneity identity), or report the exact first missing.
No fake iso, no new hypothesis, no change of objects.

## Result (short)

**The chart identification is a theorem; the S1937 first missing datum is inhabited.**
EXIT=0, zero errors, zero warnings, axioms [propext, Classical.choice, Quot.sound] on every
probed declaration, no 'sorry'/'admit'/'axiom'.  The file is

    tmp/sheaf/xif/paper/S1946ChartAlgEquivActual.lean
    SHA256 0B0D4D614081A30EFBBF1B7864474BE485502B397E645D44164F032EFD77E447
    olean .lake/build/lib/lean/tmp/sheaf/xif/paper/S1946ChartAlgEquivActual.olean
          (858424 bytes, SHA256 66B8D7A72EC260E9E91793F90FF82CE0510F5481F5808BD7EA784CFE3C7B2359)

Scope is exactly S1937's own: conditional only on [GradedRing (CohomGr (R := S1726K) Wang)].
The other S1937 residual (density of the affine chart, reduced there to IsDomain W) is not
touched and is not needed for the chart identification.

## What is proved (Lean, kernel-closed)

Chart ring and its coordinates:

* Xbar : W (class of X), Ybar = S1937Ybar (class of Y), Zbar (class of Z, S1925)
* XZ : Away WGr Zbar, YZ : Away WGr Zbar   (X/Z and Y/Z)
* chartEval : MvPolynomial (Fin 3) F' ->a[F'] Away  (evaluation at (X/Z, Y/Z, 1))
* dehom : MvPolynomial (Fin 3) F' ->a[F'] MvPolynomial (Fin 2) F'   (dehomogenization)
* dehom_Wang : dehom Wang = S1726AffinePolynomial   (Z = 1 dehomogenizes Wang to the
  affine Weierstrass polynomial; this is why both chart maps are well defined)

The homogeneity identity (the mathematical core):

* mk_add_zp, mk_smul_zp, mk_monomial_eq : the localization bookkeeping
  X^a Y^b Z^c / Z^(a+b+c) = (X/Z)^a (Y/Z)^b
* homogeneousSubmodule_eq_span_monomial : the degree-n homogeneous polynomials are spanned
  by the degree-n monomials
* chart_fraction_eq_mk (n) (p) (hp : p.IsHomogeneous n) :
      algebraMap _ _ (chartEval p) = Localization.mk (quo Wang p) (zp n)
  i.e. p(X,Y,Z)/Z^n = p(X/Z, Y/Z, 1) in the localization at Z (proved by span induction:
  monomials, additivity, F'-linearity)
* chartEval_eq_mk : the same identity inside Away:
      chartEval p = Away.mk WGr Zbar_mem_one n (quo Wang p) _

The two chart maps:

* dehomEval : MvPolynomial (Fin 3) F' ->+* R'   (evaluation at (x,y,1))
* dehomHom : W ->+* R'    (dehomogenization at Z = 1, well defined by dehom_Wang)
* dehomHom_Zbar : dehomHom Zbar = 1
* phi : Away WGr Zbar ->+* R'   (dehomHom extended along IsLocalization / awayLift,
  i.e. the localization at Z where Z is a unit)
* phi_mk : phi (Away.mk .. n a _) = dehomHom a
* phi_XZ : phi XZ = x,   phi_YZ : phi YZ = y
* chartEval2 : MvPolynomial (Fin 2) F' ->a[F'] Away   (evaluation at (X/Z, Y/Z))
* chartEval2_affinePolynomial : chartEval2 S1726AffinePolynomial = 0   (via the homogeneity
  identity at p = Wang and quo Wang Wang = 0)
* psi : R' ->a[F'] Away WGr Zbar   (the inverse chart map x |-> X/Z, y |-> Y/Z)

The two inverse laws:

* phi_comp_psi : phi.comp psi.toRingHom = RingHom.id R'
* psi_surjective : Function.Surjective psi  (every element of Away is a homogeneous fraction
  a/Z^n, a in WGr n; a is the class of a homogeneous p of degree n; psi of the class of
  dehom p is a/Z^n by chartEval_eq_mk)
* psi_injective, psi_bijective

The identification and its consumer:

* chartRingEquiv : R' ≃+* Away   (bijective ring map psi, inverse phi)
* chartAlgEquiv : Away WGr Zbar ≃ₐ[F'] R'   (AlgEquiv.ofRingEquiv, using psi.commutes)
* **S1946ChartAlgEquiv : S1937ChartAlgEquiv**   (the frozen S1937 target type)
* S1946ChartAlgEquiv_XZ : S1946ChartAlgEquiv XZ = x    (the iso sends X/Z to x)
* S1946ChartAlgEquiv_YZ : S1946ChartAlgEquiv YZ = y    (and Y/Z to y; not a fake iso)
* S1946ChartIso : S1925ChartIso   (the S1925 ring-valued residual, filled)
* S1946AffineCompactification (hdense : S1925DenseChart) : S1937AffineCompactification
  S1946ChartAlgEquiv hdense   (S1937's scheme-level compactification datum now runs with
  the chart input supplied; only the density hypothesis remains an input)
* S1946Compactification_of_domain (hdom : IsDomain W) : S1913AffineCompactification
  (the scheme-level compactification of the actual affine model of E' from the single
  remaining algebraic hypothesis: the homogeneous coordinate ring is a domain, i.e. Wang
  is irreducible; the density input is discharged by S1937DenseChart_of_domain)

## Verification

* lake env lean tmp/sheaf/xif/paper/S1946ChartAlgEquivActual.lean  ->  EXIT=0 (~51 s),
  no diagnostics, axiom audit prints only [propext, Classical.choice, Quot.sound].
* olean emitted and re-checked from the artifact by the consumer probe
  tmp/sheaf/xif/paper/_S1946Consumer.lean (EXIT=0), which states
      example : Away WGr Zbar ≃ₐ[S1726K] S1726CoordinateRing := S1946ChartAlgEquiv
      example : S1937ChartAlgEquiv := S1946ChartAlgEquiv
      example : S1925ChartIso := S1946ChartIso
      example : S1946ChartAlgEquiv XZ = xAff
      example : S1946ChartAlgEquiv YZ = yAff
      example (hdense : S1925DenseChart) := S1946AffineCompactification hdense
      example (hdom : IsDomain W) := S1946Compactification_of_domain hdom
* lexical scan: no 'sorry', no 'admit', no 'axiom', no 'native_decide'.

## What remains (unchanged by this packet)

* S1937's density residual S1925DenseChart is untouched here; S1937 already reduces it to
  IsDomain W (S1937DenseChart_of_domain), i.e. to the irreducibility of Wang.
* The graded-ring structure GradedRing (CohomGr Wang) is still a hypothesis, supplied by
  S1925GradedRingOfResidual from the decomposition residual of S1925.  The chart
  identification is proved within that same scope, as S1937 states it.