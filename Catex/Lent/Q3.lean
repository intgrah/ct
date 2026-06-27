module

public import Mathlib.CategoryTheory.Endofunctor.Algebra

@[expose] public section

open CategoryTheory Endofunctor

universe v u

/- Let F : 𝓒 ⥤ 𝓒 be an endofunctor on a category 𝓒. -/
variable {𝓒 : Type u} [Category.{v} 𝓒]
variable (F : 𝓒 ⥤ 𝓒)

/--
Define an F-algebra to be a pair ⟨A, α⟩ with A an object of 𝓒 and α : F(A) ⟶ A a morphism of 𝓒.
Define an F-homomorphism h : ⟨A, α⟩ → ⟨B, β⟩ from an F-algebra ⟨A, α⟩ to an F-algebra ⟨B, β⟩ to
be a morphism h : A → B of 𝓒 such that the following diagram commutes:

    F(A) ---F(h)---> F(B)
     |                |
     α                β
     |                |
     V                V
     A ------h------> B

Let F-alg be the category with objects F-algebras, morphisms F-homomorphisms, and identities
and compositions as in 𝓒.

If ⟨I, ι⟩ is an initial object of F-alg then ι : F(I) → I is an isomorphism in 𝓒.
-/
theorem lambek (I : Algebra F) (hi : Limits.IsInitial I) : IsIso I.str := by
  let FI : Algebra F := ⟨F.obj I.a, F.map I.str⟩
  -- Construct the F-homomorphism from the initial object I to FI
  let ⟨f, hf⟩ : I ⟶ FI := hi.to FI
  -- Let g be f pre-composed with I.str
  let g : I ⟶ I := ⟨f ≫ I.str, by rw [Functor.map_comp, ← Category.assoc, ← hf]⟩
  -- Any two morphisms from an initial object are equal, so g is just the identity
  have hg : g = 𝟙 I := hi.hom_ext g (𝟙 I)
  -- Show that f is the inverse of I.str
  refine ⟨f, ?_, ?_⟩
  · calc I.str ≫ f
      _ = F.map f ≫ FI.str := hf.symm
      _ = F.map (f ≫ I.str) := (Functor.map_comp F f I.str).symm
      _ =  F.map (𝟙 I.a) := congrArg (F.map ·.f) hg
      _ = 𝟙 (F.obj I.a) := Functor.map_id F I.a
  · calc f ≫ I.str
      _ = g.f := rfl
      _ = 𝟙 I.a := congrArg (·.f) hg

/-- This is also in mathlib -/
example (I : Algebra F) : Limits.IsInitial I → IsIso I.str :=
  Algebra.Initial.str_isIso
