module bi (A : Set) where

open import Agda.Primitive
open import Prelude.Decidable
open import Prelude.List renaming ([] to ⟨⟩)
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Stream

open List
  using (_++_)
open Stream
  renaming (module Stream to point)
  using (take)

-- a choice sequence, or point in the universal spread
point : Set
point = Stream A
{-# DISPLAY Stream A = point #-}

-- a finite approximation of a choice sequence (a neighborhood / open set)
neigh : Set
neigh = List A
{-# DISPLAY List A = neigh #-}

_⌢_ : neigh → A → neigh
⟨⟩ ⌢ x = x ∷ ⟨⟩
(x ∷ U) ⌢ y = x ∷ (U ⌢ y)

-- From a point, make an observation of a particular precision
_[_] : point → Nat → neigh
α [ n ] = take n α
{-# DISPLAY take n α = α [ n ] #-}

-- A point lies in an open set when the latter is a prefix of the former
data _∈_ : point → neigh → Set where
  ⟨⟩ : ∀ {α} → α ∈ ⟨⟩
  step : ∀ {α : point} {U} → point.tail α ∈ U → α ∈ (point.head α ∷ U)

∈-step-back : {α : point} {U : neigh} {m : A} → α ∈ (U ⌢ m) → α ∈ U
∈-step-back {U = ⟨⟩} p = ⟨⟩
∈-step-back {U = ._ ∷ U} (step p) = ? -- step (∈-step-back p)

species : Set (lsuc lzero)
species = neigh → Set

_⊑_ : species → species → Set
𝔄 ⊑ 𝔅 =
  {U : neigh}
    → 𝔄 U
    → 𝔅 U

-- A species of neighborhoods can be viewed as a collection of points,
-- so we notation for quantifying over points in a species.
infix 0 ∀∈
∀∈ : (U : neigh) (P : point → Set) → Set
∀∈ U P = (α : point) → α ∈ U → P α
syntax ∀∈ U (λ α → P) = ∀[ α ∈ U ] P

-- First, we fix an extensional/semantic explanation of what it means for
-- a species [𝔅] to bar a node [U], written [̄⊨ U ◃ 𝔅]. When [U] is in [𝔅],
-- we say that [U] is *secured*; when [𝔅] bars [U], we say that [U] is
-- *securable*.
⊨_◃_ : neigh → species → Set
⊨ U ◃ 𝔅 = ∀[ α ∈ U ] Σ[ Nat ∋ n ] 𝔅 (α [ n ])

-- Next, a syntactic/proof-theoretic characterization of securability inferences is
-- defined. Proofs are infinitely-broad wellfounded trees.
data ⊢_▹_ (𝔅 : species) : neigh → Set where
  -- [U] is secured.
  η : ∀ {U} → 𝔅 U → ⊢ 𝔅 ▹ U

  -- [U] is securable because all of its immediate children are securable.
  ϝ : ∀ {U} → (∀ x → ⊢ 𝔅 ▹ (U ⌢ x)) → ⊢ 𝔅 ▹ U

⊢_◃_ : (U : neigh) (𝔅 : species) → Set
⊢ U ◃ 𝔅 = ⊢ 𝔅 ▹ U
{-# DISPLAY ⊢_▹_ 𝔅 U = ⊢ U ◃ 𝔅 #-}

-- Fix a decidable bar [𝔅].
module _ (𝔅 : species) (𝔅? : ∀ U → Decidable (𝔅 U)) where
  -- The crux of the bar principle is essentially a completeness theorem:
  -- if [𝔅] bars [U], then we have a proof that it does. We can implement
  -- the procedure for completeness effectively, but in order to prove that
  -- it is a total function, we would need bar induction (which we are
  -- in the process of proving).
  {-# TERMINATING #-}
  brouwer's-dogma
    : (U : neigh)
    → ⊨ U ◃ 𝔅
    → ⊢ U ◃ 𝔅
  brouwer's-dogma U p with 𝔅? U
  brouwer's-dogma U p | ⊕.inl q =
    ϝ λ t →
      brouwer's-dogma
        (U ⌢ t)
        (λ α → p α Π.⟔ ∈-step-back)
  brouwer's-dogma U p | ⊕.inr q = η q

  module BI (𝔄 : species) (𝔅⊑𝔄 : 𝔅 ⊑ 𝔄) (hered : ∀ U → (∀ m → 𝔄 (U ⌢ m)) → 𝔄 U) where
    replace
      : (U : neigh)
      → (⊢ U ◃ 𝔅)
      → 𝔄 U
    replace U (η 𝔅[U]) = 𝔅⊑𝔄 𝔅[U]
    replace U (ϝ 𝒟) = hered U (λ m → replace (U ⌢ m) (𝒟 m))

    bar-induction
      : ⊨ ⟨⟩ ◃ 𝔅
      → 𝔄 ⟨⟩
    bar-induction p =
      replace ⟨⟩
        (brouwer's-dogma ⟨⟩ p)
