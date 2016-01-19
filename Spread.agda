module Spread where

open import Prelude.List
open import Prelude.Stream
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Families

open Stream public
  renaming (module Stream to Point)
  renaming (Stream to Point)
  using (head)
  using (tail)
  using (take)

open List public
  renaming (module List to Neigh)
  renaming (List to Neigh)
  renaming ([] to ⟨⟩)
  using (_++_)

module _ {A : Set} where

  _⌢_ : Neigh A → A → Neigh A
  ⟨⟩ ⌢ x = x ∷ ⟨⟩
  (x ∷ U) ⌢ y = x ∷ (U ⌢ y)

  -- From a stream make an observation of a particular precision
  _[_] : Point A → Nat → Neigh A
  α [ ze ] = []
  α [ su n ] = head α ∷ tail α [ n ]

  -- A point lies in an open set when the latter is a prefix of the former
  data _∈_ : Point A → Neigh A → Set where
    stop : ∀ {α} → α ∈ ⟨⟩
    step : ∀ {α U} → tail α ∈ U → α ∈ (head α ∷ U)

  take-prefix-id : ∀ {α U} → α ∈ U → α [ List.len U ] ≡ U
  take-prefix-id {U = ⟨⟩} p = refl
  take-prefix-id {U = ._ ∷ U} (step p) rewrite take-prefix-id p = refl

  ∈-step-back : ∀ {α U m} → α ∈ (U ⌢ m) → α ∈ U
  ∈-step-back {U = ⟨⟩} p = stop
  ∈-step-back {U = ._ ∷ U} (step p) = step (∈-step-back p)

  ∈-step-forward : ∀ {α U} → α ∈ U → α ∈ (U ⌢ Stream.idx α (List.len U))
  ∈-step-forward stop = step stop
  ∈-step-forward (step p) = step (∈-step-forward p)

  -- A neighborhood can be viewed as a collection of points,
  -- so we notation for quantifying over points in a species.
  infix 0 ∀∈
  ∀∈ : (U : Neigh A) (P : ℘ (Point A)) → Set
  ∀∈ U P = (α : Point A) → α ∈ U → P α
  syntax ∀∈ U (λ α → P) = ∀[ α ∈ U ] P
