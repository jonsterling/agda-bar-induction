module Spread where

open import Prelude.List
open import Prelude.Stream
open import Prelude.Natural
open import Prelude.Size

open Stream public
  renaming (module Stream to Point ; Stream to Point)
  using (take)

open List public
  renaming (module List to Neigh ; List to Neigh ; [] to ⟨⟩)
  using (_++_)

module _ {A : Set} where

  _⌢_ : Neigh A → A → Neigh A
  ⟨⟩ ⌢ x = x ∷ ⟨⟩
  (x ∷ U) ⌢ y = x ∷ (U ⌢ y)

  -- From a stream make an observation of a particular precision
  _[_] : Point A → Nat → Neigh A
  α [ n ] = take n α
  {-# DISPLAY take n α = α [ n ] #-}

  -- A point lies in an open set when the latter is a prefix of the former
  data _∈_ ..{sp}..{sn} : Point {sp} A → Neigh {sn} A → Set where
    ⟨⟩
      : ∀ {α}
      → _∈_ {sp}{sn} α ⟨⟩
    step
      : ∀ ..{sp′ : Size.< sp}..{sn′ : Size.< sn}
      → ∀ {α : Point {sp} A} {U : Neigh {sn′} A}
      → _∈_ {sp′}{sn′} (Point.tail α) U
      → _∈_ {sp }{sn } α (Point.head α ∷ U)

  ∈-step-back : ∀ ..{sp}..{sn} {α : Point {sp} A} {U : Neigh {sn} A} {m : A} → α ∈ (U ⌢ m) → α ∈ U
  ∈-step-back {U = ⟨⟩} p = ⟨⟩
  ∈-step-back {U = ._ ∷ U} (step p) = step (∈-step-back p)
