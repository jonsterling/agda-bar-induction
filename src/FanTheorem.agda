module FanTheorem where

open import Agda.Primitive

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Families
open import Prelude.Finite
import Prelude.Inspect as Inspect
open import Prelude.List
open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Stream
open import Prelude.Path

open import BarTheorem 𝟚
open import Spread

open Fin renaming (⊆nat to ∣_∣)

to-nat-max-id₁
  : (m n : Nat) (i : Fin m)
  → ∣ i ∣ ≡ ∣ (max-inl {m = m} {n = n} i) ∣
to-nat-max-id₁ ze ze ()
to-nat-max-id₁ ze (su n) ()
to-nat-max-id₁ (su m) ze i = refl
to-nat-max-id₁ (su m) (su n) ze = refl
to-nat-max-id₁ (su m) (su n) (su i) rewrite to-nat-max-id₁ m n i = refl

to-nat-max-id₂
  : (m n : Nat) (i : Fin n)
  → ∣ i ∣ ≡ ∣ (max-inr {m = m} {n = n} i) ∣
to-nat-max-id₂ m ze ()
to-nat-max-id₂ ze (su n) i = refl
to-nat-max-id₂ (su m) (su n) ze = refl
to-nat-max-id₂ (su m) (su n) (su i) rewrite to-nat-max-id₂ m n i = refl

++-pivot-id
  : {A : Set} (U : Neigh A) {V : Neigh A} {m : A}
  → (U ⌢ m ++ V) ≡ (U ++ m ∷ V)
++-pivot-id ⟨⟩ = refl
++-pivot-id (x ∷ U) = ≡.ap¹ (x ∷_) (++-pivot-id U)

module _ (𝔅 : ℘ (Neigh 𝟚)) (𝔅? : ∀ U → Decidable (𝔅 U)) (⊨⟨⟩◃𝔅 : ⊨ ⟨⟩ ◃ 𝔅) where
  open BI 𝔅 𝔅?

  𝔄 : Neigh 𝟚 → Set
  𝔄 U =
    Σ[ Nat ∋ k ]
    ∀ (α : Point 𝟚) →
    Σ[ Fin k ∋ n ]
      𝔅 (U ++ (α [ ∣ n ∣ ]))

  𝔅⊑𝔄 : 𝔅 ⊑ 𝔄
  𝔅⊑𝔄 𝔅[U] =
    1 ▸ λ α →
      ze ▸
        ≡.coe*
          𝔅
          (List.⊢.ρ⇒ _ ≡.⁻¹)
          𝔅[U]

  𝔄-hered : (U : Neigh 𝟚) → ((b : 𝟚) → 𝔄 (U ⌢ b)) → 𝔄 U
  𝔄-hered U φ with φ tt | φ ff
  𝔄-hered U φ | kᵗ ▸ φᵗ | kᶠ ▸ φᶠ = su ⨆k ▸ modulus
    where
      ⨆k : Nat
      ⨆k = Nat.max kᵗ kᶠ

      modulus : (α : Point 𝟚) → Σ[ Fin (su ⨆k) ∋ n ] 𝔅 (U ++ α [ ∣ n ∣ ])
      modulus α with φᵗ (tail α) | φᶠ (tail α)
      modulus α | _ | _ with head α | Inspect.inspect head α
      modulus α | m ▸ ψᵗ | _ | tt | Inspect.[ α₀≡tt ] =
        su max-inl m ▸
          ≡.coe*
            𝔅
            (≡.ap¹ (λ z → U ++ α [ su z ]) (to-nat-max-id₁ kᵗ _ m)
               ≡.⟔ ++-pivot-id U
               ≡.⟔ ≡.ap¹ (λ z → U ⌢ z ++ tail α [ ∣ m ∣ ]) α₀≡tt ≡.⁻¹)
            ψᵗ
      modulus α | _ | n ▸ ψᶠ | ff | Inspect.[ α₀≡ff ] =
        su max-inr {m = kᵗ} n ▸
          ≡.coe*
            𝔅
            (≡.ap¹ (λ z → U ++ α [ su z ]) (to-nat-max-id₂ kᵗ _ n)
              ≡.⟔ ++-pivot-id U
              ≡.⟔ ≡.ap¹ (λ z → U ⌢ z ++ tail α [ ∣ n ∣ ]) α₀≡ff ≡.⁻¹)
            ψᶠ

  fan-theorem : Σ[ Nat ∋ k ] ∀ α → Σ[ Fin k ∋ n ] 𝔅 (α [ ∣ n ∣ ])
  fan-theorem =
    bar-induction
      𝔄
      𝔅⊑𝔄
      𝔄-hered
      ⊨⟨⟩◃𝔅
