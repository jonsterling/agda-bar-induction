module Species where

open import Agda.Primitive

℘ : ∀ {ℓ} (A : Set ℓ) → Set (lsuc lzero ⊔ ℓ)
℘ A = A → Set

_⊑_ : ∀ {ℓ} {A : Set ℓ} → ℘ A → ℘ A → Set ℓ
𝔄 ⊑ 𝔅 =
  {U : _}
    → 𝔄 U
    → 𝔅 U
