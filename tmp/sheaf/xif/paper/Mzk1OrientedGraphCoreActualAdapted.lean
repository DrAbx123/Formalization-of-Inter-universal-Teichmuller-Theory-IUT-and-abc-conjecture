/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: oriented graph core facts (opposite involutive, hom composition) -/

namespace LeanFormal.IUT.XiFPaper.OrientedGraphCoreActual

universe u

structure OGraph where
  V : Type u
  E : V → V → Type u

def ogOpposite (G : OGraph.{u}) : OGraph.{u} where
  V := G.V
  E X Y := G.E Y X

@[simp] theorem ogOpposite_V (G : OGraph.{u}) : G.ogOpposite.V = G.V := rfl

@[simp] theorem ogOpposite_E (G : OGraph.{u}) (X Y : G.V) :
    G.ogOpposite.E X Y = G.E Y X := rfl

theorem ogOpposite_opposite (G : OGraph.{u}) : G.ogOpposite.ogOpposite = G := rfl

structure OGraphHom (G H : OGraph.{u}) where
  toFun : G.V → H.V
  map : ∀ {X Y : G.V}, G.E X Y → H.E (toFun X) (toFun Y)

def ogHomId (G : OGraph.{u}) : OGraphHom G G where
  toFun X := X
  map e := e

def ogHomComp {G H K : OGraph.{u}} (f : OGraphHom G H) (g : OGraphHom H K) :
    OGraphHom G K where
  toFun X := g.toFun (f.toFun X)
  map e := g.map (f.map e)

@[simp] theorem ogHomId_toFun {G : OGraph.{u}} (X : G.V) : (ogHomId G).toFun X = X := rfl

@[simp] theorem ogHomComp_toFun {G H K : OGraph.{u}} (f : OGraphHom G H)
    (g : OGraphHom H K) (X : G.V) : (ogHomComp f g).toFun X = g.toFun (f.toFun X) := rfl

@[simp] theorem ogHomComp_map {G H K : OGraph.{u}} (f : OGraphHom G H)
    (g : OGraphHom H K) {X Y : G.V} (e : G.E X Y) :
    (ogHomComp f g).map e = g.map (f.map e) := rfl

end LeanFormal.IUT.XiFPaper.OrientedGraphCoreActual
