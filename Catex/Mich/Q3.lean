module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finite.Prod

@[expose] public section

open CategoryTheory Limits

universe u

def Ent (A B : Type u) : Type u := Multiset A → B → Prop

namespace Ent

def lift {A B : Type u} (R : A → B → Prop) : Ent A B := fun as b => ∃ a, as = {a} ∧ R a b

def Ax (A : Type u) : Ent A A := lift (· = ·)

structure CompObj {A B : Type u} (f : Ent A B) where
  la : Multiset A
  b : B
  r : f la b

def comp {A B C : Type u} (f : Ent A B) (g : Ent B C) : Ent A C :=
  fun as c => ∃ lp : Multiset (CompObj f), g (lp.map CompObj.b) c ∧ as = (lp.map CompObj.la).sum

@[ext]
theorem ext {A B : Type u} {f g : Ent A B} (h : ∀ as b, f as b ↔ g as b) : f = g := by
  funext as b
  ext
  exact h as b

theorem comp_id {A B : Type u} (f : Ent A B) : comp f (Ax B) = f := by
  ext as c
  refine ⟨?_, ?_⟩
  · rintro ⟨lp, ⟨a, hbs, rfl⟩, rfl⟩
    obtain ⟨x, rfl, rfl⟩ := Multiset.map_eq_singleton.mp hbs
    simpa using x.r
  · intro h
    exact ⟨{⟨as, c, h⟩}, ⟨c, by simp, rfl⟩, by simp⟩

theorem id_comp {A B : Type u} (f : Ent A B) : comp (Ax A) f = f := by
  ext as b
  refine ⟨?_, ?_⟩
  · rintro ⟨lp, hb, rfl⟩
    have key : (lp.map CompObj.la).sum = lp.map CompObj.b := by
      have hla : lp.map CompObj.la = (lp.map CompObj.b).map fun a => ({a} : Multiset A) := by
        rw [Multiset.map_map]
        exact Multiset.map_congr rfl fun o _ => by obtain ⟨a, hla, rfl⟩ := o.r; exact hla
      rw [hla, Multiset.sum_map_singleton]
    rw [key]; exact hb
  · intro h
    refine ⟨as.map fun a => ⟨{a}, a, ⟨a, rfl, rfl⟩⟩, ?_, ?_⟩
    · simpa [Multiset.map_map] using h
    · simp [Multiset.map_map]

theorem map_eq_add {γ β : Type u} (φ : γ → β) (x : Multiset β) :
    ∀ {s : Multiset γ} {y : Multiset β}, s.map φ = x + y →
      ∃ s₁ s₂, s = s₁ + s₂ ∧ s₁.map φ = x ∧ s₂.map φ = y := by
  induction x using Multiset.induction with
  | empty => intro s y h; exact ⟨0, s, by simp, by simp, by simpa using h⟩
  | cons b x' ih =>
    intro s y h
    have hb : b ∈ s.map φ := by rw [h]; simp
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.cons_add] at h
    obtain ⟨s₁, s₂, rfl, h1, h2⟩ := ih ((Multiset.cons_inj_right _).mp h)
    exact ⟨a ::ₘ s₁, s₂, by rw [Multiset.cons_add], by rw [Multiset.map_cons, h1], h2⟩

theorem split {γ δ β : Type u} (φ : γ → β) (ψ : δ → Multiset β) (T : Multiset δ) :
    ∀ {s : Multiset γ}, s.map φ = (T.map ψ).sum →
      ∃ U : Multiset ((p : δ) ×' (blk : Multiset γ) ×' blk.map φ = ψ p),
        (U.map fun x => x.1) = T ∧ (U.map fun x => x.2.1).sum = s := by
  induction T using Multiset.induction with
  | empty =>
    intro s h
    obtain rfl : s = 0 := by simpa using h
    exact ⟨0, by simp, by simp⟩
  | cons a T' ih =>
    intro s h
    rw [Multiset.map_cons, Multiset.sum_cons] at h
    obtain ⟨s₁, s₂, rfl, h1, h2⟩ := map_eq_add φ (ψ a) h
    have ⟨U, hfst, hsnd⟩ := ih h2
    exact ⟨⟨a, s₁, h1⟩ ::ₘ U, by rw [Multiset.map_cons, hfst],
      by rw [Multiset.map_cons, Multiset.sum_cons, hsnd]⟩

theorem map_sum {γ δ : Type u} (φ : γ → δ) (V : Multiset (Multiset γ)) :
    V.sum.map φ = (V.map fun blk => blk.map φ).sum := by
  induction V using Multiset.induction with
  | empty => simp
  | cons blk V ih =>
    rw [Multiset.sum_cons, Multiset.map_add, ih, Multiset.map_cons, Multiset.sum_cons]

theorem sum_map_sum {γ δ : Type u} (φ : γ → Multiset δ) (V : Multiset (Multiset γ)) :
    (V.sum.map φ).sum = (V.map fun blk => (blk.map φ).sum).sum := by
  induction V using Multiset.induction with
  | empty => simp
  | cons blk V ih =>
    rw [Multiset.sum_cons, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_cons,
      Multiset.sum_cons]

theorem assoc {A B C D : Type u} (f : Ent A B) (g : Ent B C) (h : Ent C D) :
    comp (comp f g) h = comp f (comp g h) := by
  ext as d
  refine ⟨?_, ?_⟩
  · rintro ⟨lp, hph, rfl⟩
    refine ⟨(lp.map fun o => o.r.choose).sum, ⟨lp.map fun o =>
        ⟨o.r.choose.map CompObj.b, o.b, o.r.choose_spec.left⟩, ?_, ?_⟩, ?_⟩
    · rw [Multiset.map_map]; exact hph
    · rw [map_sum, Multiset.map_map, Multiset.map_map]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun _ _ => rfl)
    · rw [sum_map_sum, Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun o _ => (Classical.choose_spec o.r).2)
  · rintro ⟨lq, ⟨lr, hrh, hlr⟩, rfl⟩
    have ⟨U, hfst, hsnd⟩ := split CompObj.b CompObj.la lr hlr
    refine ⟨U.map fun ⟨ρ, blk, hp⟩ => ⟨(blk.map CompObj.la).sum, ρ.b, blk,
        by rw [hp]; exact ρ.r, rfl⟩, ?_, ?_⟩
    · convert hrh using 2
      rw [Multiset.map_map, ← hfst, Multiset.map_map]
      exact Multiset.map_congr rfl fun _ _ => rfl
    · rw [← hsnd, sum_map_sum, Multiset.map_map, Multiset.map_map]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun _ _ => rfl)

theorem comp_lift {A B C : Type u} (f : Ent A B) (S : B → C → Prop) :
    comp f (lift S) = fun as c => ∃ b, f as b ∧ S b c := by
  ext as c
  refine ⟨?_, ?_⟩
  · rintro ⟨lp, ⟨b', hbs, hS⟩, rfl⟩
    obtain ⟨x, rfl, rfl⟩ := Multiset.map_eq_singleton.mp hbs
    exact ⟨x.b, by simpa using x.r, hS⟩
  · intro ⟨b, hf, hS⟩
    exact ⟨{⟨as, b, hf⟩}, ⟨b, by simp, hS⟩, by simp⟩

end Ent

structure EntCat : Type (u + 1) where
  carrier : Type u

namespace EntCat

instance : CoeSort EntCat (Type u) where
  coe := EntCat.carrier

instance : Category.{u, u + 1} EntCat where
  Hom A B := Ent A B
  id A := Ent.Ax A
  comp f g := Ent.comp f g
  id_comp := Ent.id_comp
  comp_id := Ent.comp_id
  assoc := Ent.assoc

@[ext] theorem hom_ext {A B : EntCat} {f g : A ⟶ B} (h : ∀ as b, f as b ↔ g as b) : f = g :=
  Ent.ext h

open Ent

instance : HasTerminal EntCat := by
  refine (IsTerminal.ofUniqueHom (Y := ⟨PEmpty⟩)
    (fun X => ?_) (fun X m => ?_)).hasTerminal
  · nofun
  · funext _ b; exact b.elim

theorem not_initial : ¬HasInitial EntCat := by
  intro
  let f₁ : ⊥_ EntCat ⟶ ⟨PUnit⟩ := fun _ _ => True
  let f₂ : ⊥_ EntCat ⟶ ⟨PUnit⟩ := fun _ _ => False
  have e : f₁ = f₂ := initialIsInitial.hom_ext f₁ f₂
  simpa [f₁, f₂] using congrArg (· 0 PUnit.unit) e

instance (A B : EntCat) : HasBinaryProduct A B := by
  refine HasLimit.mk ⟨BinaryFan.mk (lift fun x a => x = Sum.inl a)
      (lift fun x b => x = Sum.inr b),
    BinaryFan.IsLimit.mk _ (fun f g ts => Sum.elim (f ts) (g ts)) ?_ ?_ ?_⟩
  · intro _ f g
    change comp (fun ts => Sum.elim (f ts) (g ts)) (lift fun x a => x = Sum.inl a) = f
    rw [comp_lift]
    ext as a
    simp
  · intro _ f g
    change comp (fun ts => Sum.elim (f ts) (g ts)) (lift fun x b => x = Sum.inr b) = g
    rw [comp_lift]
    ext as b
    simp
  · intro _ f g m h₁ h₂
    change comp m (lift fun x a => x = Sum.inl a) = f at h₁
    change comp m (lift fun x b => x = Sum.inr b) = g at h₂
    rw [comp_lift] at h₁ h₂
    ext ts ab
    cases ab with
    | inl a => simpa using congrFun (congrFun h₁ ts) a
    | inr b => simpa using congrFun (congrFun h₂ ts) b

instance : HasBinaryProducts EntCat := hasBinaryProducts_of_hasLimit_pair EntCat

theorem filterMap_const_none {α β : Type u} (s : Multiset α) :
    s.filterMap (fun _ => (none : Option β)) = 0 := by
  induction s using Multiset.induction with
  | empty => rfl
  | cons a s ih => rw [Multiset.filterMap_cons_none _ _ rfl, ih]

theorem sum_split {C X : Type u} (l : Multiset (C ⊕ X)) :
    (l.filterMap Sum.getRight?).map Sum.inr + (l.filterMap Sum.getLeft?).map Sum.inl = l := by
  induction l using Multiset.induction with
  | empty => simp
  | cons a l ih =>
    cases a with
    | inl c =>
      rw [Multiset.filterMap_cons_none (Sum.inl c) l rfl,
        Multiset.filterMap_cons_some Sum.getLeft? (Sum.inl c) l rfl,
        Multiset.map_cons, Multiset.add_cons, ih]
    | inr x =>
      rw [Multiset.filterMap_cons_some Sum.getRight? (Sum.inr x) l rfl,
        Multiset.filterMap_cons_none (Sum.inr x) l rfl,
        Multiset.map_cons, Multiset.cons_add, ih]

theorem finite_of_finite_powerset {α : Type u} (h : Finite (α → Bool)) : Finite α :=
  open Classical in
  Finite.of_injective (fun a => (decide <| a = ·)) fun a b hab => by
    simpa using congrFun hab b

theorem multiset_finite {α : Type u} (h : Finite (Multiset α)) : IsEmpty α := by
  by_contra hne
  obtain ⟨a⟩ := not_isEmpty_iff.mp hne
  have : Infinite (Multiset α) := Infinite.of_injective (Multiset.replicate · a) fun m n hmn => by
    simpa using congrArg Multiset.card hmn
  exact not_finite (Multiset α)

theorem not_coproducts : ¬HasBinaryCoproducts EntCat := by
  intro
  let A : EntCat := ⟨PEmpty⟩
  let P : EntCat := ⟨PUnit⟩
  let T := A ⨿ A
  have e1 : (A ⨿ A ⟶ P) ≃ (A ⟶ P) × (A ⟶ P) :=
    { toFun := fun h => (coprod.inl ≫ h, coprod.inr ≫ h)
      invFun := fun (p₁, p₂) => coprod.desc p₁ p₂
      left_inv := fun h => coprod.hom_ext (coprod.inl_desc _ _) (coprod.inr_desc _ _)
      right_inv := fun p => Prod.ext (coprod.inl_desc _ _) (coprod.inr_desc _ _) }
  have eAP : (A ⟶ P) ≃ Prop :=
    { toFun := fun f => f 0 PUnit.unit
      invFun := fun p _ _ => p
      left_inv := fun f => by
        funext s u
        obtain rfl : s = 0 := Multiset.eq_zero_of_forall_notMem fun x _ => x.elim
        rfl
      right_inv := fun _ => rfl }
  have eHom : (A ⨿ A ⟶ P) ≃ (Multiset T → Bool) :=
    { toFun := fun h s => Equiv.propEquivBool (h s PUnit.unit)
      invFun := fun g s _ => Equiv.propEquivBool.symm (g s)
      left_inv := fun h => by
        funext s u
        obtain rfl : u = PUnit.unit := Subsingleton.elim u PUnit.unit
        simp
      right_inv := fun g => by funext s; simp }
  have eFinal : Bool × Bool ≃ (Multiset T → Bool) :=
    (e1.trans (Equiv.prodCongr (eAP.trans Equiv.propEquivBool)
      (eAP.trans Equiv.propEquivBool))).symm.trans eHom
  have : IsEmpty T := multiset_finite (finite_of_finite_powerset (Finite.of_equiv _ eFinal))
  have : Unique (Multiset T) :=
    ⟨⟨0⟩, fun s => Multiset.eq_zero_of_forall_notMem fun x _ => isEmptyElim x⟩
  have : Fintype.card (Bool × Bool) = Fintype.card Bool :=
    Fintype.card_congr (eFinal.trans (Equiv.funUnique (Multiset T) Bool))
  simp at this

def expEquiv (C X Y : Type u) :
    Ent (C ⊕ X) Y ≃ Ent C (Multiset X × Y) where
  toFun e l := fun (p₁, p₂) => e (p₁.map Sum.inr + l.map Sum.inl) p₂
  invFun e l := fun y => e (l.filterMap Sum.getLeft?) (l.filterMap Sum.getRight?, y)
  left_inv e := by funext l y; simp only; rw [sum_split]
  right_inv e := by
    funext l ⟨mx, y⟩
    simp only [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def,
      Sum.getLeft?_inr, Sum.getLeft?_inl, Sum.getRight?_inr, Sum.getRight?_inl,
      filterMap_const_none, Multiset.filterMap_some, zero_add, add_zero]

end EntCat
