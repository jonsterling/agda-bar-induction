module bi (A : Set) where

open import Prelude.Decidable
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Natural
open import Prelude.Size

open import Spread
open import Species

-- A species of neighborhoods can be viewed as a collection of points,
-- so we notation for quantifying over points in a species.
infix 0 ∀∈
∀∈ : (U : Neigh A) (P : Point A → Set) → Set
∀∈ U P = (α : Point A) → α ∈ U → P α
syntax ∀∈ U (λ α → P) = ∀[ α ∈ U ] P

-- First, we fix an extensional/semantic explanation of what it means for
-- a species [𝔅] to bar a node [U], written [̄⊨ U ◃ 𝔅]. When [U] is in [𝔅],
-- we say that [U] is *secured*; when [𝔅] bars [U], we say that [U] is
-- *securable*.
⊨_◃_ : Neigh A → ℘ (Neigh A) → Set
⊨ U ◃ 𝔅 =
  ∀[ α ∈ U ]
  Σ[ Nat ∋ n ]
    𝔅 (α [ n ])

-- Next, a syntactic/proof-theoretic characterization of securability inferences is
-- defined. Proofs are infinitely-broad wellfounded trees.
data ⊢_◃_ (U : Neigh A) (𝔅 : ℘ (Neigh A)) : Set where
  -- [U] is secured.
  η : 𝔅 U → ⊢ U ◃ 𝔅

  -- [U] is securable because all of its immediate children are securable.
  ϝ : (∀ x → ⊢ (U ⌢ x) ◃ 𝔅) → ⊢ U ◃ 𝔅

syntax ϝ (λ x → 𝒟) = ϝ x ↦ 𝒟

-- Fix a decidable bar [𝔅].
module _ (𝔅 : ℘ (Neigh A)) (𝔅? : ∀ U → Decidable (𝔅 U)) where
  -- The crux of the bar principle is essentially a completeness theorem:
  -- if [𝔅] bars [U], then we have a proof that it does. We can implement
  -- the procedure for completeness effectively, but in order to prove that
  -- it is a total function, we would need bar induction (which we are
  -- in the process of proving).
  {-# TERMINATING #-}
  completeness
    : (U : Neigh A)
    → ⊨ U ◃ 𝔅
    → ⊢ U ◃ 𝔅
  completeness U p with 𝔅? U
  completeness U p | ⊕.inl q =
    ϝ t ↦
      completeness
        (U ⌢ t)
        (λ α → p α Π.⟔ ∈-step-back)
  completeness U p | ⊕.inr q = η q

  module BI (𝔄 : ℘ (Neigh A)) (𝔅⊑𝔄 : 𝔅 ⊑ 𝔄) (hered : ∀ U → (∀ m → 𝔄 (U ⌢ m)) → 𝔄 U) where
    replace
      : (U : Neigh A)
      → (⊢ U ◃ 𝔅)
      → 𝔄 U
    replace U (η 𝔅[U]) = 𝔅⊑𝔄 𝔅[U]
    replace U (ϝ 𝒟[_]) = hered U λ m → replace (U ⌢ m) 𝒟[ m ]

    bar-induction
      : ⊨ ⟨⟩ ◃ 𝔅
      → 𝔄 ⟨⟩
    bar-induction p =
      replace ⟨⟩
        (completeness ⟨⟩ p)
