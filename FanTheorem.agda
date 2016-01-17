module FanTheorem where

open import Agda.Primitive

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Families
open import Prelude.Finite
import Prelude.Inspect as Inspect
open import Prelude.List.Unsized
open import Prelude.Monoidal.Coproduct
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Natural
open import Prelude.Stream
open import Prelude.Path

open import BarTheorem 𝟚
open import Spread

open Σ using (_,_)
open Fin renaming (to-nat to ∣_∣)

to-nat-max-coh₁
  : (m n : Nat) (i : Fin m)
  → ∣ i ∣ ≡ ∣ (max-inj₁ {m = m} {n = n} i) ∣
to-nat-max-coh₁ ze ze ()
to-nat-max-coh₁ ze (su n) ()
to-nat-max-coh₁ (su m) ze i = refl
to-nat-max-coh₁ (su m) (su n) ze = refl
to-nat-max-coh₁ (su m) (su n) (su i) rewrite to-nat-max-coh₁ m n i = refl

to-nat-max-coh₂
  : (m n : Nat) (i : Fin n)
  → ∣ i ∣ ≡ ∣ (max-inj₂ {m = m} {n = n} i) ∣
to-nat-max-coh₂ m ze ()
to-nat-max-coh₂ ze (su n) i = refl
to-nat-max-coh₂ (su m) (su n) ze = refl
to-nat-max-coh₂ (su m) (su n) (su i) rewrite to-nat-max-coh₂ m n i = refl

++-swap-center
  : {A : Set} (U : Neigh A) {V : Neigh A} {m : A}
  → (U ⌢ m ++ V) ≡ (U ++ m ∷ V)
++-swap-center ⟨⟩ = refl
++-swap-center (x ∷ U) = ≡.ap¹ (x ∷_) (++-swap-center U)

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
    1 , λ α →
      ze , ≡.coe* 𝔅 (≡.inv (List.++-idn-r _)) 𝔅[U]

  𝔄-hered : (U : Neigh 𝟚) → ((b : 𝟚) → 𝔄 (U ⌢ b)) → 𝔄 U
  𝔄-hered U φ with φ tt | φ ff
  𝔄-hered U φ | a , φ[a] | b , φ[b] = su (Nat.max a b) , lemma
    where
      lemma : (α : Point 𝟚) → Σ[ Fin (su (Nat.max a b)) ∋ n ] 𝔅 (U ++ α [ ∣ n ∣ ])
      lemma α with φ[a] (tail α) | φ[b] (tail α)
      lemma α | m , ψ₀ | n , ψ₁ with head α | Inspect.inspect head α
      lemma α | m , ψ₀ | n , ψ₁ | ff | Inspect.[ α₀≡ff ] =
        su max-inj₂ {m = a} n ,
          ≡.coe*
            𝔅
            (≡.ap¹ (λ z → U ++ _ ∷ tail α [ z ]) (to-nat-max-coh₂ a b n)
              ≡.⟔ ++-swap-center U)
            (≡.coe*
              (λ z → 𝔅 ((U ⌢ z) ++ (tail α [ ∣ n ∣ ])))
              (≡.inv α₀≡ff)
            ψ₁)
      lemma α | m , ψ₀ | n , ψ₁ | tt | Inspect.[ α₀≡tt ] =
        (su max-inj₁ m) ,
          ≡.coe*
            𝔅
            (≡.ap¹ (λ z → U ++ _ ∷ tail α [ z ]) (to-nat-max-coh₁ a b m)
              ≡.⟔ ++-swap-center U
              ≡.⟔ ≡.ap¹ (λ x → (U ⌢ x) ++ tail α [ ∣ m ∣ ]) (≡.inv α₀≡tt))
            ψ₀

  fan-theorem : Σ[ Nat ∋ k ] ∀ α → Σ[ Fin k ∋ n ] 𝔅 (α [ ∣ n ∣ ])
  fan-theorem =
    bar-induction
      𝔄
      𝔅⊑𝔄
      𝔄-hered
      ⊨⟨⟩◃𝔅
