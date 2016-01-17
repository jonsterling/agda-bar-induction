module FanTheorem where

open import Agda.Primitive

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Families
open import Prelude.Finite
open import Prelude.List.Unsized
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Natural
open import Prelude.Stream
open import Prelude.Path

open import BarTheorem 𝟚
open import Spread

open Σ using (_,_)

∣_∣ : ∀ {k} → Fin k → Nat
∣ ze ∣ = ze
∣ su i ∣ = su ∣ i ∣

++-⟨⟩-id : {A : Set} (U : Neigh A) → (U ++ ⟨⟩) ≡ U
++-⟨⟩-id ⟨⟩ = refl
++-⟨⟩-id (x ∷ U) = ≡.ap¹ (λ V → x ∷ V) (++-⟨⟩-id U)

max : Nat → Nat → Nat
max m n with m Nat.≤? n
max m n | ⊕.inl _ = n
max m n | ⊕.inr _ = m

max-inj₁ : {a b : Nat} → Fin a → Fin (max a b)
max-inj₁ = {!!}

max-inj₂ : {a b : Nat} → Fin b → Fin (max a b)
max-inj₂ = {!!}

module _ (𝔅 : ℘ {ℓ₁ = lzero} (Neigh 𝟚)) (𝔅? : ∀ U → Decidable (𝔅 U)) (⊨⟨⟩◃𝔅 : ⊨ ⟨⟩ ◃ 𝔅) where
  open BI 𝔅 𝔅?

  𝔄 : Neigh 𝟚 → Set
  𝔄 U = Σ[ Nat ∋ k ] ∀ α → Σ[ Fin k ∋ n ] 𝔅 (U ++ (α [ ∣ n ∣ ]))

  𝔅⊑𝔄 : 𝔅 ⊑ 𝔄
  𝔅⊑𝔄 {U} 𝔅[U] =
    1 , λ α →
      ze , ≡.coe* 𝔅 (≡.inv (++-⟨⟩-id U)) 𝔅[U]

  𝔄-hered : (U : Neigh 𝟚) → ((b : 𝟚) → 𝔄 (U ⌢ b)) → 𝔄 U
  𝔄-hered U φ with φ tt | φ ff
  𝔄-hered U φ | a , φ[a] | b , φ[b] = su (max a b) , lemma
    where
      lemma : (α : Point 𝟚) → Σ[ Fin (su (max a b)) ∋ n ] 𝔅 (U ++ α [ ∣ n ∣ ])
      lemma α with φ[a] (Point.tail α) | φ[b] (Point.tail α)
      lemma α | m , ψ₀ | n , ψ₁ with Stream.idx α 0
      lemma α | m , ψ₀ | n , ψ₁ | ff = (su max-inj₂ {a = a} n) , {!!}
      lemma α | m , ψ₀ | n , ψ₁ | tt = (su max-inj₁ m) , {!!}

  fan-theorem : Σ[ Nat ∋ k ] ∀ α → Σ[ Fin k ∋ n ] 𝔅 (α [ ∣ n ∣ ])
  fan-theorem =
    bar-induction
      𝔄
      𝔅⊑𝔄
      𝔄-hered
      ⊨⟨⟩◃𝔅
