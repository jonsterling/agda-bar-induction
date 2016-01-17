module bi (A : Set) where

open import Agda.Primitive
open import Prelude.Natural
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Coproduct
open import Prelude.Decidable
open import Prelude.Path

-- a choice sequence, or point in the universal spread
record point : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : point

-- a finite approximation of a choice sequence (a neighborhood / open set)
data neigh : Set where
  ⟨⟩ : neigh
  _∷_ : A → neigh → neigh

_⌢_ : neigh → A → neigh
⟨⟩ ⌢ x = x ∷ ⟨⟩
(x ∷ U) ⌢ y = x ∷ (U ⌢ y)

_++_ : neigh → neigh → neigh
⟨⟩ ++ V = V
(x ∷ U) ++ V = x ∷ (U ++ V)

-- From a point, make an observation of a particular precision
_[_] : point → Nat → neigh
α [ ze ] = ⟨⟩
α [ su n ] = point.hd α ∷ ((point.tl α) [ n ])

-- A point lies in an open set when the latter is a prefix of the former
data _∈_ : point → neigh → Set where
  [] : ∀ {α} → α ∈ ⟨⟩
  step : ∀ {α : point} {U} → point.tl α ∈ U → α ∈ (point.hd α ∷ U)

species : Set (lsuc lzero)
species = neigh → Set

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
data ⊢_◃_ : neigh → species → Set where
  -- [U] is secured.
  η : ∀ {U 𝔅} → 𝔅 U → ⊢ U ◃ 𝔅

  -- [U ⌢ x] is securable, because [U] is securable.
  ζ[_] : ∀ {U 𝔅} x → ⊢ U ◃ 𝔅 → ⊢ (U ⌢ x) ◃ 𝔅

  -- [U] is securable because all of its immediate children are securable.
  ϝ : ∀ {U 𝔅} → (∀ x → ⊢ (U ⌢ x) ◃ 𝔅) → ⊢ U ◃ 𝔅

-- Brouwer shows that ζ-inferences can be normalized out of barhood proofs.
data ⊩_◃_ (U : neigh) (𝔅 : species) : Set where
  -- [U] is secured.
  η : 𝔅 U → ⊩ U ◃ 𝔅

  -- [U] is securable because all of its immediate children are securable.
  ϝ : (∀ x → ⊩ (U ⌢ x) ◃ 𝔅) → ⊩ U ◃ 𝔅

-- A bar is monotonic if every refinement of a secured neighborhood is
-- also secured.
mono : species → Set
mono 𝔅 = ∀ U x → 𝔅 U → 𝔅 (U ⌢ x)

mono-++ : species → Set
mono-++ 𝔅 = ∀ U V → 𝔅 U → 𝔅 (U ++ V)

-- Fix a monotonic bar [𝔅].
module _ (𝔅 : species) (𝔅-mono : mono 𝔅) where
  -- Then securability is monotonic.
  ⊩-mono : mono (⊩_◃ 𝔅)
  ⊩-mono U x (η 𝔅[U]) = η (𝔅-mono U x 𝔅[U])
  ⊩-mono U x (ϝ 𝒟[_]) = ϝ λ y → ⊩-mono (U ⌢ x) y 𝒟[ x ]

  -- Brouwer's normalization of securability prooofs, following Dummett.
  normalize : ∀ {U} → ⊢ U ◃ 𝔅 → ⊩ U ◃ 𝔅
  normalize (η x) = η x
  normalize (ζ[ x ] 𝒟) = ⊩-mono _ x (normalize 𝒟)
  normalize (ϝ 𝒟[_]) = ϝ λ y → normalize 𝒟[ y ]

  -- The crux of the bar principle is essentially a completeness theorem:
  -- if [𝔅] bars [U], then we have a proof that it does.
  brouwer's-dogma
    : {U : neigh}
    → ⊨ U ◃ 𝔅
    → ⊢ U ◃ 𝔅
  brouwer's-dogma p =
    {!!}
