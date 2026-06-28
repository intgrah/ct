module

public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

open CategoryTheory Functor

universe u

/- For a small category 𝓒, -/
variable (𝓒 : Type u) [SmallCategory 𝓒]

/--
Define the functor H : Set^𝓒 ⥤ Set^obj(𝓒) to map:
 - on objects: a functor X : 𝓒 ⥤ Set to the indexed family of sets
   H X := {X(c) | c ∈ obj(𝓒)};
and,
 - on morphisms: a natural transformation φ : X → Y to the indexed family of functions
   H φ := {φ_c : {X(c) → 𝑌 (c) | c ∈ obj(𝓒)}
-/
def H : (𝓒 ⥤ Type u) ⥤ (Discrete 𝓒 ⥤ Type u) where
  obj X := Discrete.functor (fun c => X.obj c)
  map φ := Discrete.natTrans (fun c => φ.app c.as)

/- Prove that the functor H : Set^𝓒 → Set^obj(𝓒) has both a left and a right adjoint. -/

def H.left : (Discrete 𝓒 ⥤ Type u) ⥤ (𝓒  ⥤ Type u) where
  obj F := {
    obj c := Σ d : 𝓒, (d ⟶ c) × F.obj ⟨d⟩
    map {c c'} g := ↾fun ⟨d, f, x⟩ => ⟨d, f ≫ g, x⟩
  }
  map {F G} α := {
    app c := ↾fun ⟨d, f, x⟩ => ⟨d, f, α.app ⟨d⟩ x⟩
  }

def H.leftAdjunction : H.left 𝓒 ⊣ H 𝓒 :=
  .mkOfUnitCounit {
    unit := {
      app F := {
        app c := ↾fun x => ⟨c.as, 𝟙 c.as, x⟩
        naturality := by
          intro ⟨X⟩ ⟨Y⟩ ⟨f⟩
          obtain rfl := Discrete.eq_of_hom ⟨f⟩
          simp
      }
    }
    counit := {
      app X := {
        app c := ↾fun ⟨d, f, x⟩ => X.map f x
        naturality {c c'} g := by
          ext ⟨d, f, x⟩
          exact Functor.map_comp_apply X f g x
      }
      naturality {X Y} f := by
        ext c ⟨d, g, x⟩
        change (f.app d ≫ Y.map g) x = (X.map g ≫ f.app c) x
        rw [f.naturality g]
    }
    left_triangle := by
      ext F c ⟨d, f, x⟩
      change (⟨d, 𝟙 d ≫ f, x⟩ : Σ d : 𝓒, (d ⟶ c) × F.obj ⟨d⟩) = ⟨d, f, x⟩
      rw [Category.id_comp]
    right_triangle := by
      ext X c y
      change X.map (𝟙 c.as) y = y
      rw [Functor.map_id_apply]
  }

def H.right : (Discrete 𝓒 ⥤ Type u) ⥤ (𝓒  ⥤ Type u) where
  obj F := {
    obj c := ∀ d : 𝓒, (c ⟶ d) → F.obj ⟨d⟩
    map {c c'} g := ↾fun α d h => α d (g ≫ h)
  }
  map {F G} fg := {
    app c := ↾fun β d f => fg.app ⟨d⟩ (β d f)
  }

def H.rightAdjunction : H 𝓒 ⊣ H.right 𝓒 :=
  .mkOfUnitCounit {
    unit := {
      app Y := {
        app c := ↾fun y d f => Y.map f y
        naturality {c c'} g := by
          ext y
          funext d h
          exact (Functor.map_comp_apply Y g h y).symm
      }
      naturality {X Y} f := by
        ext c y
        funext d g
        change (f.app c ≫ Y.map g) y = (X.map g ≫ f.app d) y
        rw [f.naturality g]
    }
    counit := {
      app F := {
        app c := ↾fun α => α c.as (𝟙 c.as)
        naturality := by
          intro ⟨X⟩ ⟨Y⟩ ⟨f⟩
          obtain rfl := Discrete.eq_of_hom ⟨f⟩
          simp
      }
    }
    left_triangle := by
      ext p c f
      change p.map (𝟙 c.as) f = f
      rw [Functor.map_id_apply]
    right_triangle := by
      ext p c f
      funext d g
      change f d (g ≫ 𝟙 d) = f d g
      rw [Category.comp_id]
  }

instance : IsRightAdjoint (H 𝓒) := ⟨⟨H.left 𝓒, ⟨H.leftAdjunction 𝓒⟩⟩⟩
instance : IsLeftAdjoint (H 𝓒) := ⟨⟨H.right 𝓒, ⟨H.rightAdjunction 𝓒⟩⟩⟩
