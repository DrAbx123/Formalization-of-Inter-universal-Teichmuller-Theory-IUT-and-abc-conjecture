# Signifier / Signified Registry

Purpose: do not collapse different typographic symbols into one Lean identifier.
Method: PyMuPDF `rawdict` gives each character's font and bbox; page drawings
give horizontal underline segments; count segments under each char.  Samples
were checked against rendered pages.  Raw dump:
`D:\lean\tmp\paper_pages\symbol_lexicon_raw.txt`.

Font families (CM = Computer Modern):
- CMMI*: math italic
- CMBX*/CMMIB*: bold / bold math italic
- CMSY*: math symbols / calligraphic
- MSBM*: AMS blackboard bold
- EUFM*: Euler fraktur
- CMR*/CMTI*: roman / text italic

## Distinctions that must be preserved

| Paper signifier | Visual form | Paper meaning | Lean object | Status |
|---|---|---|---|---|
| q_v | CMMI10 q, ONE underline under q; v CMMI7 one underline | q-parameter q_v | `PaperQParameter` | OK after symbol types |
| q_v | CMMI10 q, TWO underlines under q; v one underline | 2l-th root of q_v | `PaperQRoot` | OK after symbol types |
| q | plain CMMI10, no underline | generic q in prose/function, or q in q-parameter phrase | not a value automatically | must be context-typed |
| F | CMMI10 italic F | number field F | `K` / `T.arithmetic.F` | separate by type |
| F_l | MSBM10 blackboard F + CMMI l | finite field F_l | `Fl l` / `ZMod l` | separate by type; verify |
| F | CMSY10 script F | Frobenioid / script F | `Frobenioid` (not field F) | naming collision risk |
| F⊩, F⊢, F⊣ | CMSY F with decorations | prime-strip variants | `FPrimeStrip` variants | verify one type per decoration |
| O | CMSY10 script O | ring of integers | `CompletionIntegers` / integral closure | separate |
| Θ | uppercase CMR10 | Θ-pilot / Θ-link / theta function object | `Theta...` | uppercase only |
| θ | lowercase CMMI10 | theta function/values, local theta | `theta...` | lowercase only |
| μ | CMMIB/CMMI μ | roots of unity / group μ | `rootsOfUnity` | separate μ_2l vs μ(F_mod^×) |
| v | CMMI7 underlined | bad-reduction place (v ∈ V_bad) | `Bad` / underlined V | `CompletionValuedSourceGeometry.V` is generic; FIX |
| v | CMMI10 no underline | generic place | `V` / finite place | separate from bad v |
| |F_l| / F_l^× / F_l^⋇ | quotient/subsets of F_l | label carriers | `SignedLabel` is NOT the quotient; FIX |

## Current Lean collapses found

1. `SignedLabel` contains both j and -j; theta(j)=theta(-j).  It is not the
   paper label quotient `|F_l| = F_l/{±1}`.  Fixed for root theta by
   `ThetaLabel = {j // 0<j}`; all other consumers must migrate.
2. `CompletionValuedSourceGeometry.V` is a generic place type.  It does not
   encode the underlined bad place `v`; `qVFamily` uses `Bad`, but the new
   geometry does not.  Two `v` signifiers are collapsed.  FIX: use a bad-place
   index or an explicit `UnderlinedPlace` wrapper.
3. `qUnit` is a bare unit type.  The name does not say whether it is the
   single-underlined q-parameter or the double-underlined root.  `PaperQParameter`
   and `PaperQRoot` now separate them; all old `qUnit` consumers must migrate.
4. `paperThetaImagePoint` / `paperThetaHull` in `PaperC3TensorBlockActual`
   operate on q-parameter powers qUnit^(j²), not the double-underlined root.
   The name collapses the signifier.  Consuming files must not treat these as
   paper theta.
5. `F` names: number field F, finite field F_l, Frobenioid script F, and
   prime-strip F⊩ are different signs.  Lean has separate types but the local
   names `K`, `Fmod`, `Fl`, `FPrimeStrip` are close; an import-level audit must
   check that no theorem identifies them accidentally.
6. `Θ` vs `θ`: Lean is case-sensitive, but names like `thetaPacket` and
   `ThetaPilotCarrier` mixed in one namespace.  A consumer can confuse the
   theta function with the Theta-pilot object; type audit needed.
7. `μ_{2l}` (roots of unity in the local field) vs `μ(F_mod^×)` (roots of
   unity in the finite field) are different carriers.  Current `rootsOfUnity`
   uses both; check that no comparison identifies them without a map.

## Required discipline

- A Lean identifier must name exactly one paper signifier/type.
- No implicit coercion between `PaperQParameter` and `PaperQRoot`.
- Root values are used only up to the `mu_{2l}` orbit.
- Theta labels use `ThetaLabel` (0<j), not all `SignedLabel`.
- Underlined bad `v` must be typed as `Bad`/underlined place, not arbitrary V.
- Decorated F/D prime-strips and Θ/θ objects must remain distinct types.
