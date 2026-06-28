module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

@[expose] public section

open CategoryTheory Opposite MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped CartesianClosed

universe v u

/- Let R be an object of a cartesian closed category 𝓒. -/
variable {𝓒 : Type u} [Category.{v, u} 𝓒] [CartesianMonoidalCategory 𝓒] [MonoidalClosed 𝓒]
variable (R : 𝓒)

/-- Recall the functor R^(−) : 𝓒ᵒᵖ ⥤ 𝓒 mapping an object X of 𝓒 to the exponential object R^X of 𝓒,
and a morphism f : Z → Y of 𝓒 to the morphism R^f = cur (app ◦ (id_{R^Y} × f)) : R^Y → R^Z -/
def expFunctor : 𝓒ᵒᵖ ⥤ 𝓒 where
  obj X := X.unop ⟹ R
  map {Y Z} f :=
    let Y : 𝓒 := Y.unop
    let Z : 𝓒 := Z.unop
    let f : Z ⟶ Y := f.unop
    -- Mathlib convention places the exponential on the right,
    -- rather than on the left, like in the question
    let app : Y ⊗ (Y ⟹ R) ⟶ R := uncurry (𝟙 (Y ⟹ R))
    -- Hence we tensor on the right
    (curry ((f ⊗ₘ 𝟙 (Y ⟹ R)) ≫ app) : (Y ⟹ R) ⟶ (Z ⟹ R))
  map_id := by simp
  map_comp {X Y Z} f g := by
    have eq_pre {A B : 𝓒} (h : A ⟶ B) :
        curry ((h ⊗ₘ 𝟙 (B ⟹ R)) ≫ uncurry (𝟙 (B ⟹ R))) = (MonoidalClosed.pre h).app R := by
      rw [tensorHom_id, ← curry_uncurry ((MonoidalClosed.pre h).app R),
        ← Category.id_comp ((MonoidalClosed.pre h).app R), MonoidalClosed.uncurry_pre_app]
    simp only [unop_comp, eq_pre, MonoidalClosed.pre_map, NatTrans.comp_app]

@[simp]
theorem expFunctor_map {X Y : 𝓒ᵒᵖ} (f : X ⟶ Y) :
    (expFunctor R).map f = (MonoidalClosed.pre f.unop).app R := by
  change curry ((f.unop ⊗ₘ 𝟙 _) ≫ uncurry (𝟙 (X.unop ⟹ R))) = _
  rw [tensorHom_id, ← curry_uncurry ((MonoidalClosed.pre f.unop).app R),
    ← Category.id_comp ((MonoidalClosed.pre f.unop).app R), MonoidalClosed.uncurry_pre_app]

/-- We could also define it using the internal hom functor -/
example : expFunctor R = MonoidalClosed.internalHom.flip.obj R := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) fun X Y f => heq_of_eq ?_
  rw [expFunctor_map]
  rfl

/-- The left adjoint to expFunctor R, mapping Y ↦ (Y ⟹ R). -/
def expFunctorLeftAdjoint : 𝓒 ⥤ 𝓒ᵒᵖ where
  obj Y := op (Y ⟹ R)
  map f := ((MonoidalClosed.pre f).app R).op

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory toSymmetricCategory in
def expFunctorAdjunction : expFunctorLeftAdjoint R ⊣ expFunctor R :=
  Adjunction.mkOfHomEquiv {
    homEquiv Y X := {
      toFun f := curry ((β_ X.unop Y).hom ≫ uncurry f.unop)
      invFun g := (curry ((β_ Y X.unop).hom ≫ uncurry g)).op
      left_inv f := by simp [expFunctorLeftAdjoint]
      right_inv g := by simp [expFunctorLeftAdjoint]
    }
    homEquiv_naturality_left_symm {Y' Y X} f g := by
      apply Quiver.Hom.unop_inj
      dsimp only [Equiv.coe_fn_symm_mk]
      simp only [unop_comp, expFunctorLeftAdjoint, expFunctor]
      rw [uncurry_natural_left, ← Category.assoc (β_ Y' X.unop).hom,
        ← BraidedCategory.braiding_naturality_left, Category.assoc]
      exact (MonoidalClosed.curry_pre_app f _).symm
    homEquiv_naturality_right {Y X X'} f g := by
      dsimp only [Equiv.coe_fn_mk]
      simp only [unop_comp, expFunctor_map, expFunctorLeftAdjoint]
      rw [uncurry_natural_left, ← Category.assoc (β_ X'.unop Y).hom,
        ← BraidedCategory.braiding_naturality_left, Category.assoc]
      exact (MonoidalClosed.curry_pre_app g.unop _).symm
  }
