/- PORTED DONOR FILE (grace): tmp/TauCeti/TauCeti/RingTheory/AdjoinRoot/Minpoly.lean (TauCeti, Apache-2.0).
   Changes only: imports rewritten (TauCeti modules -> our ported files in tmp/sheaf/xif/paper; Mathlib kept),
   no other changes. -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.AdjoinRoot

-- DUPLICATE: kept as a source snapshot only; NOT an active dependency.
-- Canonical source: tmp/external/ported/tauceti_belyi_core (consumers must import that).

/-!
# Minimal polynomials of classes in `AdjoinRoot`

For polynomials `f` and `g` over a field `K`, the class `AdjoinRoot.mk f g` is the value `g(α)` at
the root `α` of `f`. Its minimal polynomial over `K` is the polynomial whose roots are the images
under `g` of the roots of `f` when `f` is irreducible: it divides `p` exactly when
`f ∣ p.comp g`, which for squarefree `f` says that `g` maps the roots of `f` into the roots of
`p`. It is irreducible of degree at most `deg f`.

## Main results

* `AdjoinRoot.minpoly_mk_dvd_iff`: `minpoly K (mk f g) ∣ p ↔ f ∣ p.comp g`.
* `AdjoinRoot.natDegree_minpoly_mk_le`: for `f ≠ 0`, the minimal polynomial has degree at most
  `f.natDegree`.
* `AdjoinRoot.irreducible_minpoly_mk`: for `f` irreducible, the minimal polynomial is irreducible.
* `AdjoinRoot.minpoly_root_of_monic`: over any commutative ring, the minimal polynomial of the
  adjoined root of a monic `f` is `f`.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K]