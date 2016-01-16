module bi where

open import Agda.Primitive
open import Prelude.Natural
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Coproduct
open import Prelude.Decidable
open import Prelude.Path

module space (A : Set) where
  record point : Set where
    coinductive
    constructor _∷_
    field
      hd : A
      tl : point

  data neigh : Set where
    ⟨⟩ : neigh
    _⌢_ : neigh → A → neigh

  _∶_ : A → neigh → neigh
  x ∶ ⟨⟩ = ⟨⟩ ⌢ x
  x ∶ (U ⌢ y) = (x ∶ U) ⌢ y

{-
  _++_ : neigh → neigh → neigh
  U ++ ⟨⟩ = U
  U ++ (V ⌢ x) = (U ++ V) ⌢ x
  -}

  _++_ : neigh → neigh → neigh
  ⟨⟩ ++ V = V
  (U ⌢ x) ++ V = U ++ (x ∶ V)

  ++-⌢-id : ∀ {U V} {x} → U ++ (V ⌢ x) ≡ (U ++ V) ⌢ x
  ++-⌢-id {⟨⟩} {V} = λ {x} → refl
  ++-⌢-id {U ⌢ x} {V} = ++-⌢-id {U} {x ∶ V}

  ++-⟨⟩-id : {U : neigh} → U ++ ⟨⟩ ≡ U
  ++-⟨⟩-id {⟨⟩} = refl
  ++-⟨⟩-id {U ⌢ x} rewrite ++-⌢-id {U} {⟨⟩} {x} | ++-⟨⟩-id {U} = refl

  _‼_ : point → Nat → A
  α ‼ ze = point.hd α
  α ‼ (su n) = point.tl α ‼ n

  _[_] : point → Nat → neigh
  α [ ze ] = ⟨⟩
  α [ su n ] = (α [ n ]) ⌢ (α ‼ n)

  data _∈_ : point → neigh → Set where
    [] : ∀ {α} → α ∈ ⟨⟩
    step : ∀ {α : point} {U} → point.tl α ∈ U → α ∈ (point.hd α ∶ U)

{-
  ∈-hereditary : {α : point} {U : neigh} {x : A} → α ∈ (U ⌢ x) → α ∈ U
  ∈-hereditary {U = []} p = []
  ∈-hereditary {U = x ∷ U} p = {!!}
  -}

  species : Set (lsuc lzero)
  species = neigh → Set

  ∀∈ : (U : neigh) (P : point → Set) → Set
  ∀∈ U P = (α : point) → α ∈ U → P α
  syntax ∀∈ U (λ α → P) = ∀[ α ∈ U ] P

  _◃_ : neigh → species → Set
  U ◃ 𝔅 = ∀[ α ∈ U ] (Σ[ Nat ∋ n ] 𝔅 (α [ n ]))

  data ⊢_◃_ : neigh → species → Set where
    η : ∀ {U 𝔅} → 𝔅 U → ⊢ U ◃ 𝔅
    ζ[_] : ∀ {U 𝔅} x → ⊢ U ◃ 𝔅 → ⊢ (U ⌢ x) ◃ 𝔅
    ϝ : ∀ {U 𝔅} → (∀ x → ⊢ (U ⌢ x) ◃ 𝔅) → ⊢ U ◃ 𝔅

  data ⊩_◃_ : neigh → species → Set where
    η : ∀ {U 𝔅} → 𝔅 U → ⊩ U ◃ 𝔅
    ϝ : ∀ {U 𝔅} → (∀ x → ⊩ (U ⌢ x) ◃ 𝔅) → ⊩ U ◃ 𝔅

  monotonic : species → Set
  monotonic 𝔅 = ∀ U x → 𝔅 U → 𝔅 (U ⌢ x)

  monotonic-++ : species → Set
  monotonic-++ 𝔅 = ∀ U V → 𝔅 U → 𝔅 (U ++ V)

  monotonic-⇒-monotonic-++ : {𝔅 : species} → monotonic 𝔅 → monotonic-++ 𝔅
  monotonic-⇒-monotonic-++ p U ⟨⟩ x rewrite ++-⟨⟩-id {U} = x
  monotonic-⇒-monotonic-++ p U (V ⌢ x) x₁ rewrite ++-⌢-id {U} {V} {x} = p (U ++ V) x (monotonic-⇒-monotonic-++ p U V x₁)

  module _ (𝔅 : species) (𝔅? : ∀ U → Decidable (𝔅 U)) (𝔅-mono : monotonic 𝔅) (𝔅⟨⟩ : 𝔅 ⟨⟩) where

    elim : ∀ {U} → ⊢ U ◃ 𝔅 → ⊩ U ◃ 𝔅
    elim (η p) = η p
    elim {U = V ⌢ x} (ζ[ _ ] 𝒟) = ≡.coe* (λ W → ⊩ (W ⌢ x) ◃ 𝔅) (++-⟨⟩-id {V}) (go ⟨⟩ 𝒟)
      where
        go : {V : neigh} {x : A} (W : neigh) → ⊢ V ◃ 𝔅 → ⊩ ((V ++ W) ⌢ x) ◃ 𝔅
        go {V = V} {x = x} W (η p) rewrite ≡.inv (++-⌢-id {V} {W} {x}) = η (monotonic-⇒-monotonic-++ 𝔅-mono _ (W ⌢ _) p)
        go W (ζ[ x ] 𝒟) = go (x ∶ W) 𝒟
        go {V = V} ⟨⟩ (ϝ 𝒟) rewrite ++-⟨⟩-id {V} = elim (𝒟 _)
        go {V = V} (W ⌢ x₂) (ϝ 𝒟₁) rewrite ++-⌢-id {V} {W} {x₂} = ?
    elim (ϝ 𝒟) = ϝ (λ y → elim (𝒟 y))

{-
    bar-principle
      : (U : neigh)
      → U ◃ 𝔅
      → ⊢ U [◃] 𝔅
    bar-principle U p with 𝔅? U
    bar-principle U p | ⊕.inl q with U
    bar-principle U p | ⊕.inl q | ⟨⟩ = η 𝔅⟨⟩
    bar-principle U p | ⊕.inl q | U' ⌢ x =
      ϝ λ y →
        {!!}
    bar-principle U p | ⊕.inr q = η q


open space

-}
