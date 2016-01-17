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
open import Prelude.Size
open import Prelude.Stream

open List
  using (_++_)
open Stream
  renaming (module Stream to point)
  using (take)

-- a choice sequence, or point in the universal spread
point : ..{s : Size} → Set
point {s} = Stream {s} A
{-# DISPLAY Stream A = point #-}

-- a finite approximation of a choice sequence (a neighborhood / open set)
neigh : ..{s : Size} → Set
neigh {s} = List {s} A
{-# DISPLAY List A = neigh #-}

_⌢_ : neigh → A → neigh
⟨⟩ ⌢ x = x ∷ ⟨⟩
(x ∷ U) ⌢ y = x ∷ (U ⌢ y)

-- From a point, make an observation of a particular precision
_[_] : point → Nat → neigh
α [ n ] = take n α
{-# DISPLAY take n α = α [ n ] #-}

-- A point lies in an open set when the latter is a prefix of the former
data _∈_ ..{sp}..{sn} : point {sp} → neigh {sn} → Set where
  ⟨⟩
    : ∀ {α}
    → _∈_ {sp}{sn} α ⟨⟩
  step
    : ∀ ..{sp′ : Size.< sp}..{sn′ : Size.< sn}
    → ∀ {α : point {sp}} {U : neigh {sn′}}
    → _∈_ {sp′}{sn′} (point.tail α) U
    → _∈_ {sp }{sn } α (point.head α ∷ U)

∈-step-back : ∀ ..{sp}..{sn} {α : point {sp}} {U : neigh {sn}} {m : A} → α ∈ (U ⌢ m) → α ∈ U
∈-step-back {U = ⟨⟩} p = ⟨⟩
∈-step-back {U = ._ ∷ U} (step p) = step (∈-step-back p)

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
data ⊢_◃_ (U : neigh) (𝔅 : species) : Set where
  -- [U] is secured.
  η : 𝔅 U → ⊢ U ◃ 𝔅

  -- [U] is securable because all of its immediate children are securable.
  ϝ : (∀ x → ⊢ (U ⌢ x) ◃ 𝔅) → ⊢ U ◃ 𝔅

-- Fix a decidable bar [𝔅].
module _ (𝔅 : species) (𝔅? : ∀ U → Decidable (𝔅 U)) where
  -- The crux of the bar principle is essentially a completeness theorem:
  -- if [𝔅] bars [U], then we have a proof that it does. We can implement
  -- the procedure for completeness effectively, but in order to prove that
  -- it is a total function, we would need bar induction (which we are
  -- in the process of proving).
  {-# TERMINATING #-}
  completeness
    : (U : neigh)
    → ⊨ U ◃ 𝔅
    → ⊢ U ◃ 𝔅
  completeness U p with 𝔅? U
  completeness U p | ⊕.inl q =
    ϝ λ t →
      completeness
        (U ⌢ t)
        (λ α → p α Π.⟔ ∈-step-back)
  completeness U p | ⊕.inr q = η q

  module BI (𝔄 : species) (𝔅⊑𝔄 : 𝔅 ⊑ 𝔄) (hered : ∀ U → (∀ m → 𝔄 (U ⌢ m)) → 𝔄 U) where
    replace
      : (U : neigh)
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
