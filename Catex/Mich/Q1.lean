module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

@[expose] public section

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C}

theorem section_mono (s : X ⟶ Y) [IsSplitMono s] : Mono s := inferInstance
theorem equalizer_mono (f g : X ⟶ Y) [HasEqualizer f g] : Mono (equalizer.ι f g) := inferInstance
theorem section_regular (s : X ⟶ Y) [IsSplitMono s] : IsRegularMono s := inferInstance
theorem regular_strong (m : X ⟶ Y) [IsRegularMono m] : StrongMono m := inferInstance

class ExtremalMono (m : X ⟶ Y) : Prop extends Mono m where
  isIso : ∀ {V : C} (e : X ⟶ V) (v : V ⟶ Y) [Epi e], e ≫ v = m → IsIso e

instance strong_extremal (m : X ⟶ Y) [StrongMono m] : ExtremalMono m where
  isIso e v _ fac := by
    have sq : CommSq (𝟙 X) e m v := ⟨by simpa only [Category.id_comp] using fac.symm⟩
    have : IsSplitMono e := IsSplitMono.mk' ⟨sq.lift, sq.fac_left⟩
    exact isIso_of_epi_of_isSplitMono e
