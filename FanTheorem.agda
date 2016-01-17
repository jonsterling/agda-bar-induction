module FanTheorem where

open import Agda.Primitive

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Families
open import Prelude.Finite
open import Prelude.List
open import Prelude.Monoidal.Coproduct.Indexed
open import Prelude.Natural
open import Prelude.Path

open import BarTheorem 𝟚
open import Spread

open Σ using (_,_)

-- ∀[X:(𝔹 List) ─→ ℙ]. (tbar(𝔹;X) ⇒ Decidable(X) ⇒ (∃k:ℕ. ∀f:ℕ ─→ 𝔹. ∃n:ℕk. (X map(f;upto(n)))))

∣_∣ : ∀ {k} → Fin k → Nat
∣ ze ∣ = ze
∣ su i ∣ = su ∣ i ∣

++-⟨⟩-id : {A : Set} (U : Neigh A) → (U ++ ⟨⟩) ≡ U
++-⟨⟩-id ⟨⟩ = refl
++-⟨⟩-id (x ∷ U) = {!!} -- ≡.ap¹ (λ V → x ∷ V) (++-⟨⟩-id U)

module _ (𝔅 : ℘ {ℓ₁ = lzero} (Neigh 𝟚)) (𝔅? : ∀ U → Decidable (𝔅 U)) (⊨⟨⟩◃𝔅 : ⊨ ⟨⟩ ◃ 𝔅) where
  open BI 𝔅 𝔅?

  𝔄 : Neigh 𝟚 → Set
  𝔄 U = Σ[ Nat ∋ k ] ∀ α → Σ[ Fin k ∋ n ] 𝔅 (U ++ (α [ ∣ n ∣ ]))

  𝔅⊑𝔄 : 𝔅 ⊑ 𝔄
  𝔅⊑𝔄 {U} 𝔅[U] =
    1 , λ α →
      ze , ≡.coe* 𝔅 (≡.inv (++-⟨⟩-id U)) 𝔅[U]

  𝔄-hered : (U : Neigh 𝟚) → ((b : 𝟚) → 𝔄 (U ⌢ b)) → 𝔄 U
  𝔄-hered U φ = {!!}

  fan-theorem : Σ[ Nat ∋ k ] ∀ α → Σ[ Fin k ∋ n ] 𝔅 (α [ ∣ n ∣ ])
  fan-theorem =
    bar-induction
      𝔄
      𝔅⊑𝔄
      𝔄-hered
      ⊨⟨⟩◃𝔅
