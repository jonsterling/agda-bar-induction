-- module BarTheorem (A : Set) where
module BarTheorem (A : Set) where

open import Agda.Primitive
open import Prelude.Decidable
open import Prelude.Families
open import Prelude.List.Unsized
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Monoidal.Product
open import Prelude.Monoidal.Product.Indexed
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Stream
open import Spread

open Fam public
  renaming (_⊆_ to _⊑_)
  using ()

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

-- Fix a species [𝔅].
module _ (𝔅 : ℘ (Neigh A)) where
  -- The proof-theoretic characterization of securability is unrestrictedly sound
  -- for any species of nodes.
  soundness
    : (U : Neigh A)
    → ⊢ U ◃ 𝔅
    → ⊨ U ◃ 𝔅
  soundness U (η 𝔅[U]) α a∈U =
    List.len U Σ., ≡.coe* 𝔅 (take-prefix-id a∈U ≡.⁻¹) 𝔅[U]
  soundness U (ϝ 𝒟[_]) α a∈U =
    soundness (U ⌢ _) 𝒟[ _ ] α (∈-step-forward a∈U)

  -- Now, suppose that [𝔅] is decidable.
  module _ (𝔅? : ∀ U → Decidable (𝔅 U)) where

    -- The crux of the bar principle is to assert that the proof-theoretic
    -- treatment of securability is also complete! That is to say, if [𝔅]
    -- bars [U], then we have a proof that it does.
    --
    -- We can implement the procedure for completeness effectively, but in order
    -- to prove that it is a total function, we would need bar induction (which
    -- we are in the process of proving).
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

    -- Now, fix a species [𝔄] of nodes that contains every secured node such that
    -- [𝔄] is hereditary. Then, we can demonstrate an induction principle for [𝔄]:
    --
    --     if [𝔅] is a bar (i.e. [⟨⟩] is securable), then [⟨⟩] is in [𝔄]
    --
    -- The induction principle is demonstrated by first analyzing the evidence for the
    -- securability of the initial node into a proof (i.e. an ordinal), and then walking
    -- this proof and replacing every secured node with the corresponding element of [𝔄],
    -- and every (proper) securable node with an appeal to [𝔄]'s heredity.
    --
    -- In this way, the proof of securability serves as the *matrix* for the proof of the
    -- conclusion, [𝔄 ⟨⟩].
    module BI (𝔄 : ℘⁰ (Neigh A)) (𝔅⊑𝔄 : 𝔅 ⊑ 𝔄) (hered : ∀ U → (∀ m → 𝔄 (U ⌢ m)) → 𝔄 U) where
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
