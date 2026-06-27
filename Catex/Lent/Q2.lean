module

public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

open CategoryTheory Functor

universe u

/- For a small category 𝓒, -/
variable (𝓒 : Type u) [SmallCategory.{u} 𝓒]

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

@[reducible]
def H.left : (Discrete 𝓒 ⥤ Type u) ⥤ (𝓒  ⥤ Type u) where
  obj F := {
    obj c := Σ d : 𝓒, (d ⟶ c) × F.obj ⟨d⟩
    map {c c'} g := ↾fun ⟨d, f, x⟩ => ⟨d, f ≫ g, x⟩
    map_id c := calc
          (↾fun ⟨d, f, x⟩ => ⟨d, f ≫ 𝟙 c, x⟩)
        = (↾fun ⟨d, f, x⟩ => ⟨d, f, x⟩) := by simp only [Category.comp_id]
      _ = 𝟙 (Σ d : 𝓒, (d ⟶ c) × F.obj ⟨d⟩) := rfl
    map_comp {F G K} fg gk := by
      ext ⟨d, f, x⟩
      · dsimp
      · dsimp
        rw [Category.assoc]
  }
  map {F G} α := {
    app c := ↾fun ⟨d, f, x⟩ => ⟨d, f, α.app ⟨d⟩ x⟩
    naturality {X Y} f := rfl
  }
  map_id F := rfl
  map_comp {F G K} fg gk := rfl

def H.leftAdjunction : H.left 𝓒 ⊣ H 𝓒 :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app F := {
        app c := ↾fun x => ⟨c.as, 𝟙 c.as, x⟩
        naturality := by
          intro ⟨X⟩ ⟨Y⟩ ⟨f⟩
          obtain rfl := Discrete.eq_of_hom ⟨f⟩
          simp
      }
      naturality {X Y} f := rfl
    }
    counit := {
      app X := {
        app c := ↾fun ⟨d, f, x⟩ => X.map f x
        naturality {c c'} g := by
          ext ⟨d, f, x⟩
          change X.map (f ≫ g) x = X.map g (X.map f x)
          exact Functor.map_comp_apply X f g x
      }
      naturality {X Y} f := by
        ext c ⟨d, g, x⟩
        change Y.map g (f.app d x) = f.app c (X.map g x)
        calc
              Y.map g (f.app d x)
            = (f.app d ≫ Y.map g) x := rfl
          _ = (X.map g ≫ f.app c) x := by rw [f.naturality g]
          _ = f.app c (X.map g x) := rfl
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

@[reducible]
def H.right : (Discrete 𝓒 ⥤ Type u) ⥤ (𝓒  ⥤ Type u) where
  obj F := {
    obj c := ∀ d : 𝓒, (c ⟶ d) → F.obj ⟨d⟩
    map {c c'} g := ↾fun α d h => α d (g ≫ h)
  }
  map {F G} fg := {
    app c := ↾fun β d f => fg.app ⟨d⟩ (β d f)
    naturality {c c'} f := rfl
  }

def H.rightAdjunction : H 𝓒 ⊣ H.right 𝓒 :=
  Adjunction.mkOfUnitCounit {
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
        calc Y.map g (f.app c y)
            = (f.app c ≫ Y.map g) y := rfl
          _ = (X.map g ≫ f.app d) y := by rw [f.naturality g]
          _ = f.app d (X.map g y) := rfl
    }
    counit := {
      app := fun F => {
        app c := ↾fun α => α c.as (𝟙 c.as)
        naturality := by
          intro ⟨X⟩ ⟨Y⟩ ⟨f⟩
          obtain rfl := Discrete.eq_of_hom ⟨f⟩
          simp
      }
    }
    left_triangle := by
      ext p c f
      dsimp [H]
      change p.map (𝟙 c.as) f = f
      rw [Functor.map_id_apply]
    right_triangle := by
      ext p c f
      change (fun d g => f d (g ≫ 𝟙 d)) = f
      ext
      rw [Category.comp_id]
  }

instance : IsRightAdjoint (H 𝓒) := ⟨⟨H.left 𝓒, ⟨H.leftAdjunction 𝓒⟩⟩⟩
instance : IsLeftAdjoint (H 𝓒) := ⟨⟨H.right 𝓒, ⟨H.rightAdjunction 𝓒⟩⟩⟩
