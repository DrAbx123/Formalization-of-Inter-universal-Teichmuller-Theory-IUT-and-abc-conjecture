# TERM-TABLE — machine-readable expressions for componentVol/ind2/gap terms (A1081)

Status: source-level table; no compile.  Signs are as real numbers; `p` is a
rational prime, `p` finite place of `K`; `logp := Real.log p`.

## 0. Variables

| symbol | meaning | source |
|---|---|---|
| `i` | capsule index `Fin (nC D)` | `Gap.lean` |
| `p` | rational prime place | `VcI.lean` |
| `c` | tuple `Lab i → Fiber Fmod (.finite p)` | `VcI.lean` |
| `j` | tensor factor label, `j = i.1+1` | `ThetaRegion:126-136` |
| `e_{c j}` | ramification index `ramIdx K (finPart c j)` | `VcI.lean` |
| `ρ_{c j}` | `logShellRadius (finPart c j) p` | `VcI:464` |
| `w_{p,c}` | `tupleWeight p c = ∏_j weight` | `Container:338` |
| `d` | `finrank ℚ_p (Tensor K p c)` | `Volume:196` |
| `μ` | additive Haar on the tensor | `Volume:78` |
| `qOrder` | raw `v(q)` (Nat) | `Basic:171-194` |
| `A` | `|log q| = logQ/(2ℓ)` | `LeftHandSide:88` |

## 1. `componentVol` (general)

```text
componentVol(vQ,c,S) = log( μ(S) / μ(integralAt) ) / finrank(ℚ_[p], Tensor)
```
Source: `Iut/Concrete/LocalConstruct/Volume.lean:196`;
`componentVol_integral = 0` (`:201`).

| term | case | expression | sign | source |
|---|---|---|---|---|
| `componentVol(integral)` | any | `0` | 0 | `Volume:201` |
| `componentVol(a•X)` | `a` unit | `componentVol(a•integral) + componentVol(X)` | depends | `IdentifiedCopies:67` |
| `componentVol(a•integral)` | `a = incl(y)` | `-ord_p(y)·logp` (additive over factors) | `-` if `ord>0` | `ScaleVolume:118`, `:52` |
| `orderVol(p,c)` | any finite | `componentVol(order p c)` | `≤ 0` | `VcI:93`, `:102` |
| `orderVol(p,c)` | odd/unramified `e=1` all factors | `0` | 0 | `VcI:135-139` |
| `orderVol(p,c)` | general | `-Σ_j differentExponent(c j)·logp ≤ orderVol ≤ 0` | `≤0` | `VcI:111-112` |
| `shellExcess(p,c)` | any | `log( μ(⊗𝓘)/μ(order) ) / d` | depends | `VcI:158` |
| `shellExcess(p,c)` | tame odd, `e_j ≤ p−2` | `Σ_j (1 - 1/e_j)·logp` | `≥0` | `VcI:414` (`shellExcess_eq_tame`) |
| `componentVol(⊗𝓘)` | any | `shellExcess + orderVol` | sum | `VcI:165` |
| `componentVol(⊗𝓘)` | tame odd | `Σ_j (1-1/e_j)logp + orderVol` | `≥ orderVol` | `VcI:165/414` |
| `componentVol(leastHull(⊗𝓘))` | any finite | `Σ_j ρ_j·logp` | `≥0` | `VcI:603` |
| `componentVol(leastHull(⊗𝓘))` | tame odd | `Σ_j (1-1/e_j)·logp` | `≥0` | `VcI:435` |
| `componentVol(⊗𝓘)` | wild/2-adic | no closed form; use `shellExcess+orderVol`, bounds | unknown | `VcI:165/109` |

## 2. `hullPacket` / `vcIPacket`

```text
vcIPacket(i,vQ) = Σ_c w_{p,c} · componentVol(vcIComp(i,vQ,c))
hullPacket(i,vQ) = Σ_c w_{p,c} · componentVol(leastHull(vcIComp(i,vQ,c)))
```
Source: `VcI:683/689`.

| term | case | expression | sign | source |
|---|---|---|---|---|
| `hullPacket(i,.finite p)` | any finite | `Σ_c w_c Σ_j ρ_{c j}·logp` | `≥0` | `VcI:806` |
| `hullPacket(i,.finite p)` | tame odd | `Σ_c w_c Σ_j (1-1/e_{c j})·logp` | `≥0` | `VcI:844` |
| `hullPacket(i,.finite p)` | unramified e=1 | `0` | 0 | `VcI:844` with `e=1` |
| `vcIPacket(i,.finite p)` | any finite | `Σ_c w_c (shellExcess + orderVol)` | `Σ w·shell + Σ w·order` | `VcI:795` |
| `vcIPacket(i,.finite p)` | tame odd | `Σ_c w_c(Σ_j(1-1/e)logp + orderVol)` | `≥ Σ w orderVol` | `VcI:830` |
| `vcIPacket/hullPacket(i,∞)` | arch | arch log-volume (not the finite formula); `archDefect` correction | data-dependent | `Gap:459` |
| `hullPacket(i,good p)` | `p ∉ badChars` | `0` (theta hull = shell, no gap) | 0 | `Gap:945` (`gapHullAt_eq_zero`; hull side flat) |

## 3. `gapHullAt` / `ind2Term`

```text
gapHullAt(i,.finite p) = Σ_c w_{p,c}·ind2Term(i,p,c)
gapHullAt(i,∞) = 0
gapTerm(i,vQ,c) = componentVol(leastHull(thetaComponent)) - componentVol(lgpComp)
```
Source: `Gap:895/639`; `gapTerm_nonneg` (`:646`), `gapAt_nonneg` (`:657`),
`gapHullAt_nonneg` (`:937`).

| term | case | expression | sign | source |
|---|---|---|---|---|
| `ind2Term(i,p,c)` | general | `V(leastHull(thetaComponent)) - V(scaleElt • leastHull(shell))` | `≥0` | `Gap:747/756` |
| `ind2Term(i,p,c)` | `p ∉ badChars` | `0` | 0 | `Gap:771` (`ind2Term_eq_zero`) |
| `ind2Term(i,p,c)` | C0 conditional | `frac(j²·v_p(q)/(2ℓ))·logp`, `v_p(q)=qOrder/(2ℓ·e)` | `[0,logp)` | `C0-EXACT-DERIVATION`; **not Lean-proved** |
| `ind2Term(i,p,c)` | tame odd | no simplification beyond general def; use `frac` only conditionally | `≥0` | `Gap:747`, C0 gap |
| `ind2Term(i,p,c)` | wild/2-adic | general def; no closed form; `frac` formula may need `e` | `≥0` | `Gap:747` |
| `gapHullAt(i,.finite p)` | any finite | `Σ_c w_c·ind2Term` | `≥0` | `Gap:895/937` |
| `gapHullAt(i,.finite p)` | `p ∉ badChars` | `0` | 0 | `Gap:945` |
| `gapHullAt(i,∞)` | arch | `0` | 0 | `Gap:919/937` |
| `gapHullAt(i,p)` | bad/C0 conditional | `Σ_c w_c·frac(...)·logp` | `≥0` | conditional on C0 frac |
| `gapTerm(i,vQ,c)` | any | `V(hull(thetaComp)) - V(lgpComp)` | `≥0` | `Gap:639/646` |
| `archDefect(c)` | arch | `V(leastHull(logShell∞)) - V(logShell∞)` | `≥0` (pos) | `Gap:459/463/468` |

## 4. CSV (machine-readable)

```csv
term,case,expression,sign,source
componentVol,general,log(mu(S)/mu(integral))/finrank,depends,Volume:196
componentVol,integral,0,0,Volume:201
componentVol,unit_smul,comp(a*integral)+comp(X),depends,IdentifiedCopies:67
componentVol,unit_incl,-ord_p(y)*logp,minus_if_ord_pos,ScaleVolume:118
orderVol,general,componentVol(order),nonpos,VcI:93
orderVol,odd_unramified,0,0,VcI:135
orderVol,bound,-sum differentExponent*logp <= orderVol <= 0,nonpos,VcI:111
shellExcess,general,log(mu(tensorLogShell)/mu(order))/d,depends,VcI:158
shellExcess,tame_odd,sum_j (1-1/e_j)*logp,nonneg,VcI:414
componentVol_tensorLogShell,general,shellExcess+orderVol,sum,VcI:165
componentVol_tensorLogShell,tame_odd,sum_j(1-1/e_j)logp+orderVol,ge_orderVol,VcI:165+414
componentVol_hull,general,sum_j rho_j*logp,nonneg,VcI:603
componentVol_hull,tame_odd,sum_j(1-1/e_j)*logp,nonneg,VcI:435
componentVol_tensorLogShell,wild,no_closed_form_use_shellExcess_plus_orderVol,unknown,VcI:165
vcIPacket,finite,sum_c w_c*componentVol(vcIComp),depends,VcI:683
hullPacket,finite,sum_c w_c*sum_j rho_j*logp,nonneg,VcI:806
hullPacket,tame_odd,sum_c w_c*sum_j(1-1/e_j)logp,nonneg,VcI:844
hullPacket,unramified,0,0,VcI:844
vcIPacket,tame_odd,sum_c w_c*(sum_j(1-1/e)logp+orderVol),depends,VcI:830
ind2Term,general,V(leastHull(thetaComp))-V(scaleElt*leastHull(shell)),nonneg,Gap:747
ind2Term,good_p,0,0,Gap:771
ind2Term,c0_conditional,frac(j^2*v_p(q)/(2l))*logp,nonneg,not_proved_C0
gapHullAt,finite,sum_c w_c*ind2Term,nonneg,Gap:895
gapHullAt,good_p,0,0,Gap:945
gapHullAt,infinity,0,0,Gap:919
gapHullAt,bad_c0_conditional,sum_c w_c*frac(...)*logp,nonneg,conditional_C0
gapTerm,general,V(leastHull(thetaComp))-V(lgpComp),nonneg,Gap:639
archDefect,arch,V(leastHull(logShell))-V(logShell),nonneg,Gap:459
```

## 5. Notes

- `p=2`, `p=3`, wild ramification: no closed form in the tree; only the
  radius `sSup` definition and `orderVol` bounds apply.
- `arch` component: `archDefect` is only nonnegative/positive; exact value is
  not formalized (Gap header).
- `good p` (`p ∉ badChars`): `ind2Term=0`/`gapHullAt=0`; hull packet formula
  still applies but the theta values are `1` so `scaleElt=1`.
- The `frac` formula is **conditional** on `leastHull_thetaComponent_eq_pow_floor`
  (C0 gap); do not use it as a green identity.
