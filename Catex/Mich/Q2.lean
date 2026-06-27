module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.Group.Multiset

@[expose] public section

open CategoryTheory Limits

universe u

structure Obj (X : Type u) where
  A : Type u
  α : List A → A
  f : X → A
  sing : ∀ a, α [a] = a
  flat : ∀ xs : List (List A), α (xs.map α) = α xs.flatten
  perm : ∀ xs ys : List A, xs.Perm ys → α xs = α ys

variable {X : Type u}

instance : CoeSort (Obj X) (Type u) where
  coe := Obj.A

structure Hom (src tgt : Obj X) where
  h : src → tgt
  preserves_α : h ∘ src.α = tgt.α ∘ List.map h
  preserves_f : h ∘ src.f = tgt.f

theorem Hom.ext {src tgt : Obj X} : ∀ (f g : Hom src tgt), f.h = g.h → f = g
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : CoeFun (Obj X) fun a => X → a where
  coe := Obj.f

instance : Category (Obj X) where
  Hom := Hom
  id A := ⟨id, by funext xs; simp, rfl⟩
  comp {A B C} f g := ⟨g.h ∘ f.h, by
    funext xs
    calc g.h (f.h (A.α xs))
        = g.h (B.α (xs.map f.h)) := congrArg g.h (congrFun f.preserves_α xs)
      _ = C.α ((xs.map f.h).map g.h) := congrFun g.preserves_α (xs.map f.h)
      _ = C.α (xs.map (g.h ∘ f.h)) := by rw [List.map_map], by
    funext x
    calc g.h (f.h (A.f x))
        = g.h (B.f x) := congrArg g.h (congrFun f.preserves_f x)
      _ = C.f x := congrFun g.preserves_f x⟩

def FreeCommMonoid (X : Type u) : Obj X where
  A := Multiset X
  α := List.sum
  f x := {x}
  sing := by simp
  flat xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, ← List.sum_append, List.flatten_cons]
  perm xs ys hperm := hperm.sum_eq

instance : AddCommMonoid (FreeCommMonoid X) :=
  inferInstanceAs (AddCommMonoid (Multiset X))

instance : HasInitial (Obj X) := by
  apply IsInitial.hasInitial (X := FreeCommMonoid X)
  refine IsInitial.ofUniqueHom (fun T => ?_) (fun T => ?_)
  · let φ : Multiset X → T :=
      Quotient.lift (fun xs : List X => T.α (xs.map T)) fun xs ys hperm =>
        T.perm (xs.map T) (ys.map T) (hperm.map T)
    have φ_add (m₁ m₂ : Multiset X) : φ (m₁ + m₂) = T.α [φ m₁, φ m₂] :=
      Quotient.inductionOn₂ m₁ m₂ fun xs ys => by
        simpa [φ] using (T.flat [xs.map T, ys.map T]).symm
    refine ⟨φ, ?_, ?_⟩
    · funext ms
      induction ms with
      | nil => rfl
      | cons m ms ih =>
        have reassoc : T.α [φ m, T.α (ms.map φ)] = T.α (φ m :: ms.map φ) := by
          simpa [T.sing] using T.flat [[φ m], ms.map φ]
        calc φ (List.sum (m :: ms))
            = T.α [φ m, φ (List.sum ms)] := φ_add m (List.sum ms)
          _ = T.α [φ m, T.α (ms.map φ)] := by rw [show φ (List.sum ms) = T.α (ms.map φ) from ih]
          _ = T.α (φ m :: ms.map φ) := reassoc
    · funext x
      change φ {x} = T.f x
      rw [← Multiset.coe_singleton]
      change T.α ([x].map T.f) = T.f x
      simp [T.sing]
  · rintro ⟨g, hgα, hgf⟩
    apply Hom.ext
    funext ms
    induction ms using Quotient.ind with | _ xs =>
    induction xs with
    | nil => exact congrFun hgα []
    | cons x xs ih =>
      have hα := congrFun hgα [({x} : Multiset X), (xs : Multiset X)]
      have hx : g ({x} : Multiset X) = T x := congrFun hgf x
      have hih : g (xs : Multiset X) = T.α (xs.map T) := ih
      have reassoc : T.α (T x :: xs.map T) = T.α [T x, T.α (xs.map T)] := by
        simpa [T.sing] using (T.flat [[T x], xs.map T]).symm
      simpa [FreeCommMonoid, hx, hih, reassoc] using hα
