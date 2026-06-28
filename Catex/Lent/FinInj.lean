module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Card

@[expose] public section

open CategoryTheory

universe u

namespace FinInj

variable {l m n n' : ℕ} (ι : Fin m ↪ Fin n) (ι₁ : Fin l ↪ Fin m) (ι₂ : Fin m ↪ Fin n)

instance : SmallCategory ℕ where
  Hom m n := Fin m ↪ Fin n
  id n := .refl (Fin n)
  comp := .trans

instance (m n : ℕ) : FunLike (m ⟶ n) (Fin m) (Fin n) :=
  inferInstanceAs (FunLike (Fin m ↪ Fin n) (Fin m) (Fin n))

theorem le (ι : Fin m ↪ Fin n) : m ≤ n := by
   simpa using Fintype.card_le_of_injective ι ι.injective

def extendLast : Fin (m + 1) ↪ Fin (n + 1) where
  toFun := Fin.lastCases (Fin.last n) (Fin.castSucc ∘ ι)
  inj' {a b} hab := by
    cases a using Fin.lastCases <;>
    cases b using Fin.lastCases <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
    case last.last => rfl
    case last.cast j => exact absurd hab.symm (Fin.castSucc_ne_last (ι j))
    case cast.last j => exact absurd hab (Fin.castSucc_ne_last (ι j))
    case cast.cast x₁ x₂ => congr; exact ι.injective (Fin.castSucc_injective n hab)

@[simp]
theorem extendLast_id : extendLast (𝟙 n) = 𝟙 (n + 1) := by
  ext i
  cases i using Fin.lastCases <;>
  (simp [extendLast]; rfl)

@[simp]
theorem extendLast_trans : extendLast (ι₁.trans ι₂) = (extendLast ι₁).trans (extendLast ι₂) := by
  ext i
  cases i using Fin.lastCases <;> simp [extendLast]

@[simp]
theorem extendLast_last : extendLast ι (Fin.last m) = Fin.last n := by
  simp [extendLast, Fin.lastCases_last]

@[simp]
theorem castSucc_extendLast : Fin.castSuccEmb.trans (extendLast ι) = ι.trans Fin.castSuccEmb := by
  ext k
  simp [extendLast, Fin.lastCases_castSucc]

def extendVacant {j : Fin n} {ι : Fin m ↪ Fin n} (hj : ∀ i, ι i ≠ j) : Fin (m + 1) ↪ Fin n where
  toFun := Fin.lastCases j ι
  inj' {a b} hab := by
    cases a using Fin.lastCases <;>
    cases b using Fin.lastCases <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
    case last.last => rfl
    case last.cast j => exact absurd hab.symm (hj j)
    case cast.last j => exact absurd hab (hj j)
    case cast.cast x₁ x₂ => congr; exact ι.injective hab

end FinInj
