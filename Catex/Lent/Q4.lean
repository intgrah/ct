module

public import Mathlib.CategoryTheory.Monoidal.Closed.Types

public import Catex.Lent.FinInj

@[expose] public section

open CategoryTheory MonoidalCategory CartesianClosed
open FinInj

universe u

/--
Let N in Setᴵ be the covariant presheaf that includes FinInj in Set; that is:
  • N(n) = [n] = Fin n
  • N(ι) = ι : [m] → [n] for a morphism ι : m → n in I
-/
def N : ℕ ⥤ Type where
  obj n := Fin n
  map ι := ↾ι

noncomputable def Ptilde (P : ℕ ⥤ Type) : ℕ ⥤ Type where
  /-
  For a covariant presheaf P in Setᴵ, let (P̃(n) | n ∈ ℕ) be the indexed family of sets given by:
    P̃(n) = P(n)ⁿ × P(n + 1) = (Fin n → P(n)) × P(n + 1)
  -/
  obj n := (Fin n → P.obj n) × P.obj (n + 1)
  /-
  For every morphism ι : m → n in I, define a function P̃(ι) : P̃(m) → P̃(n) yielding a
  covariant presheaf P̃ in Setᴵ.
  -/
  map {m n} ι := ↾fun (f, x) =>
    let f' j :=
      if h : ∃ i, ι i = j then
        P.map ι (f h.choose)
      else
        have hj : ∀ i, ι i ≠ j := fun i hij => h ⟨i, hij⟩
        P.map (extendVacant hj) x
    (f', P.map (extendLast ι) x)
  map_id n := by
    ext ⟨f, x⟩ j
    · have h : ∃ i, 𝟙 n i = j := ⟨j, rfl⟩
      simp only [CategoryTheory.Functor.map_id, TypeCat.hom_ofHom, dif_pos h]
      exact congrArg f h.choose_spec
    · simp
  map_comp {m n p} ι₁ ι₂ := by
    ext ⟨f, x⟩ k
    · change
        (if h : ∃ i, (ι₁ ≫ ι₂) i = k then _ else _) =
        if h : ∃ j, ι₂ j = k then
          P.map ι₂ <| if h' : ∃ i, ι₁ i = h.choose then _ else _
        else _
      by_cases h_comp : ∃ i, (ι₁ ≫ ι₂) i = k
      · -- k is in range of composition
        rw [dif_pos h_comp]
        have h₂ : ∃ j, ι₂ j = k := ⟨ι₁ h_comp.choose, h_comp.choose_spec⟩
        rw [dif_pos h₂]
        have h1 : ∃ i, ι₁ i = h₂.choose := by
          use h_comp.choose
          apply ι₂.injective
          change (ι₁ ≫ ι₂) h_comp.choose = ι₂ h₂.choose
          rw [h_comp.choose_spec, h₂.choose_spec]
        rw [dif_pos h1]
        have heq : h1.choose = h_comp.choose := by
          apply ι₁.injective
          apply ι₂.injective
          calc ι₂ (ι₁ h1.choose)
              = ι₂ h₂.choose := by rw [h1.choose_spec]
            _ = k := h₂.choose_spec
            _ = (ι₁ ≫ ι₂) h_comp.choose := h_comp.choose_spec.symm
            _ = ι₂ (ι₁ h_comp.choose) := rfl
        simp only [P.map_comp, heq]
        rfl
      · rw [dif_neg h_comp]
        have h_comp' : ∀ i, (ι₁.trans ι₂) i ≠ k := not_exists.mp h_comp
        by_cases h₂ : ∃ j, ι₂ j = k
        · -- k is in range of ι₂, but not in range of composition
          rw [dif_pos h₂]
          have h₁ : ¬∃ i, ι₁ i = h₂.choose := by
            intro ⟨i, hi⟩
            apply h_comp
            use i
            change ι₂ (ι₁ i) = k
            rw [hi, h₂.choose_spec]
          rw [dif_neg h₁]
          apply not_exists.mp at h₁
          have heq : extendVacant h_comp' = (extendVacant h₁).trans ι₂ := by
            ext i
            cases i using Fin.lastCases with
            | last =>
              simpa only [extendVacant, Function.Embedding.toFun_eq_coe,
                Function.Embedding.coeFn_mk, Fin.lastCases_last, Function.Embedding.trans_apply]
              using congrArg Fin.val h₂.choose_spec.symm
            | cast j =>
              simp [extendVacant, Fin.lastCases_castSucc]
          calc P.map (extendVacant h_comp') x
              = P.map ((extendVacant h₁).trans ι₂) x := by rw [heq]
            _ = (P.map (extendVacant h₁) ≫ P.map ι₂) x := by rw [← P.map_comp]; rfl
            _ = P.map ι₂ (P.map (extendVacant h₁) x) := rfl
        · rw [dif_neg h₂]
          apply not_exists.mp at h₂
          have heq : extendVacant h_comp' = (extendLast ι₁).trans (extendVacant h₂) := by
            ext i
            cases i using Fin.lastCases <;>
            simp [extendVacant, extendLast]
          calc P.map (extendVacant h_comp') x
              = P.map ((extendLast ι₁).trans (extendVacant h₂)) x := by rw [heq]
            _ = (P.map (extendLast ι₁) ≫ P.map (extendVacant h₂)) x := by rw [← P.map_comp]; rfl
            _ = P.map (extendVacant h₂) (P.map (extendLast ι₁) x) := rfl
    · calc P.map (extendLast (ι₁.trans ι₂)) x
          = P.map ((extendLast ι₁).trans (extendLast ι₂)) x := by simp only [extendLast_trans]
        _ = (P.map (extendLast ι₁) ≫ P.map (extendLast ι₂)) x := by rw [← P.map_comp]; rfl
        _ = P.map (extendLast ι₂) (P.map (extendLast ι₁) x) := rfl

postfix:max "˜" => Ptilde

variable {P Q : ℕ ⥤ Type}

namespace Ptilde

def eval : N ⊗ P˜ ⟶ P where
  app n := ↾fun (i, f, _) => f i
  naturality {m n} ι := by
    ext ⟨i, f, x⟩
    change (if h : ∃ k, ι k = ι i then _ else _) = P.map ι (f i)
    have h : ∃ k, ι k = ι i := ⟨i, rfl⟩
    rw [dif_pos h]
    exact congrArg (fun y => P.map ι (f y)) (ι.injective h.choose_spec)

noncomputable abbrev ev : N ⊗ (N ⟹ P) ⟶ P := (ihom.ev N).app P

noncomputable abbrev forward : P˜ ⟶ N ⟹ P := MonoidalClosed.curry eval

noncomputable def backward : N ⟹ P ⟶ P˜ where
  app n := ↾fun α => {
    fst i := ev.app n (i, α)
    snd := ev.app (n + 1) (Fin.last n, (N ⟹ P).map Fin.castSuccEmb α)
  }
  naturality {m n} ι := by
    let castSuccM : Fin m ↪ Fin (m + 1) := Fin.castSuccEmb
    ext α
    apply Prod.ext
    · ext j
      dsimp
      by_cases hj : ∃ k, ι k = j
      · have : (j, (N ⟹ P).map ι α) = (ι hj.choose, (N ⟹ P).map ι α) := by
          simp only [hj.choose_spec]
        erw [this]
        change _ = if _ : ∃ i, ι i = j then _ else _
        rw [dif_pos hj]
        have key := ConcreteCategory.congr_hom (ev.naturality ι)
          ((hj.choose, α) : (N ⊗ (N ⟹ P)).obj m)
        simp only [ConcreteCategory.comp_apply] at key
        exact key
      · let vacant := extendVacant (not_exists.mp hj)
        have ext_comp : castSuccM ≫ vacant = ι := by
          change castSuccM.trans vacant = ι
          ext
          simp [vacant, extendVacant, castSuccM, Fin.lastCases_castSucc]
        have : vacant (Fin.last m) = j := by simp [vacant, extendVacant, Fin.lastCases_last]
        have : (N ⟹ P).map ι = (N ⟹ P).map castSuccM ≫ (N ⟹ P).map vacant := by
          rw [← (N ⟹ P).map_comp, ext_comp]
        have pair_eq : (j, (N ⟹ P).map ι α) =
          (vacant (Fin.last m), (N ⟹ P).map vacant ((N ⟹ P).map castSuccM α)) := by
          simp [*]
        erw [pair_eq]
        change _ = if _ : ∃ i, ι i = j then _ else _
        rw [dif_neg hj]
        have key := ConcreteCategory.congr_hom (ev.naturality vacant)
          ((Fin.last m, (N ⟹ P).map castSuccM α) : (N ⊗ (N ⟹ P)).obj (m + 1))
        simp only [ConcreteCategory.comp_apply] at key
        exact key
    · let ι' := extendLast ι
      have : castSuccM ≫ ι' = ι ≫ Fin.castSuccEmb := castSucc_extendLast ι
      have map_factor : (N ⟹ P).map ι ≫ (N ⟹ P).map Fin.castSuccEmb =
          (N ⟹ P).map castSuccM ≫ (N ⟹ P).map ι' := by
        rw [← (N ⟹ P).map_comp, ← (N ⟹ P).map_comp, this]
      have : (Fin.last n, (N ⟹ P).map Fin.castSuccEmb ((N ⟹ P).map ι α)) =
          (ι' (Fin.last m), (N ⟹ P).map ι' ((N ⟹ P).map castSuccM α)) :=
        Prod.ext (extendLast_last ι).symm (ConcreteCategory.congr_hom map_factor α)
      change ev.app (n + 1) _ = P.map (extendLast ι) _
      erw [this]
      have key := ConcreteCategory.congr_hom (ev.naturality ι')
          ((Fin.last m, (N ⟹ P).map castSuccM α) : (N ⊗ (N ⟹ P)).obj (m + 1))
      simp only [ConcreteCategory.comp_apply] at key
      exact key

noncomputable abbrev adj : tensorLeft N ⊣ ihom N :=
  ihom.adjunction N

lemma adj_eq : (tensorLeft N).map forward ≫ ev = (eval : N ⊗ P˜ ⟶ P) := by
  have hsymm : (adj.homEquiv P˜ P).symm forward = eval :=
    (adj.homEquiv P˜ P).symm_apply_apply eval
  rw [← hsymm]
  exact adj.homEquiv_symm_apply (X := P˜) (Y := P) forward

@[simp] theorem forward_backward : forward ≫ backward = 𝟙 P˜ := by
  let ev : N ⊗ (N ⟹ P) ⟶ P := (ihom.ev N).app P
  have adj_pt n i fx : ev.app n (i, forward.app n fx) = eval.app n (i, fx) := by
    rw [← adj_eq]
    set_option maxRecDepth 1024 in rfl
  ext n fx
  apply Prod.ext
  · ext i
    dsimp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply]
    have hback (α : (N ⟹ P).obj n) : (backward.app n α).1 i = ev.app n (i, α) := rfl
    exact (hback (forward.app n fx)).trans (adj_pt n i fx)
  · have eq_fwd : forward.app (n + 1) (P˜.map Fin.castSuccEmb fx) =
        (N ⟹ P).map Fin.castSuccEmb (forward.app n fx) := by
      have key := ConcreteCategory.congr_hom (forward.naturality Fin.castSuccEmb) fx
      simp only [ConcreteCategory.comp_apply] at key
      exact key
    have h_not : ¬∃ k, Fin.castSuccEmb k = Fin.last n := by
      intro ⟨k, hk⟩
      exact Fin.castSucc_ne_last k (by simp at hk)
    have extend_id : extendVacant (not_exists.mp h_not) = 𝟙 (n + 1) := by
      ext i
      cases i using Fin.lastCases <;> (simp [extendVacant]; rfl)
    have rhs_eq : (P˜.map Fin.castSuccEmb fx).fst (Fin.last n) = fx.snd := by
      change (if _ : ∃ i, Fin.castSuccEmb i = Fin.last n then _ else _) = fx.snd
      rw [dif_neg h_not, extend_id, P.map_id]
      rfl
    calc ((forward ≫ backward).app n fx).2
        = ev.app (n + 1) (Fin.last n, (N ⟹ P).map Fin.castSuccEmb (forward.app n fx)) := rfl
      _ = ev.app (n + 1) (Fin.last n, forward.app (n + 1) (P˜.map Fin.castSuccEmb fx)) :=
          congrArg (fun y => ev.app (n + 1) (Fin.last n, y)) eq_fwd.symm
      _ = eval.app (n + 1) (Fin.last n, P˜.map Fin.castSuccEmb fx) :=
          adj_pt (n + 1) (Fin.last n) (P˜.map Fin.castSuccEmb fx)
      _ = (P˜.map Fin.castSuccEmb fx).fst (Fin.last n) := rfl
      _ = fx.snd := rhs_eq

@[simp] theorem backward_forward : backward ≫ forward = 𝟙 (N ⟹ P) := by
  let ev : N ⊗ (N ⟹ P) ⟶ P := (ihom.ev N).app P
  have : (tensorLeft N).map (backward ≫ forward) ≫ ev = ev := by
    ext m ⟨i, β⟩
    have key : ev.app m (((tensorLeft N).map (backward ≫ forward)).app m (i, β)) =
        eval.app m (i, backward.app m β) := by
      rw [← adj_eq]
      set_option maxRecDepth 2048 in rfl
    calc ((tensorLeft N).map (backward ≫ forward) ≫ ev).app m (i, β)
        = ev.app m (((tensorLeft N).map (backward ≫ forward)).app m (i, β)) := rfl
      _ = eval.app m (i, backward.app m β) := key
      _ = ev.app m (i, β) := rfl
  apply (adj.homEquiv (N ⟹ P) P).symm.injective
  simp_all [ev, Adjunction.homEquiv_symm_apply]
  rfl

/--
Show P̃ is isomorphic to the exponential presheaf Pᴺ in Setᴵ.
-/
noncomputable def iso : P˜ ≅ N ⟹ P :=
  ⟨forward, backward, forward_backward, backward_forward⟩

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/--
Define a natural transformation app : P̃ ⊗ N ⟶ P in Setᴵ exhibiting P̃ as the exponential
Pᴺ in Setᴵ.
-/
noncomputable def app : P˜ ⊗ N ⟶ P :=
  (forward ⊗ₘ 𝟙 N) ≫ (β_ (N ⟹ P) N).hom ≫ (ihom.ev N).app P

abbrev braidEquiv : (Q ⊗ N ⟶ P) ≃ (N ⊗ Q ⟶ P) :=
  Iso.homCongr (β_ N Q).symm (Iso.refl P)

noncomputable abbrev curryEquiv : (N ⊗ Q ⟶ P) ≃ (Q ⟶ N ⟹ P) :=
  adj.homEquiv Q P

noncomputable abbrev transportEquiv : (Q ⟶ N ⟹ P) ≃ (Q ⟶ P˜) :=
  Iso.homCongr (Iso.refl Q) iso.symm

theorem app_universal (g : Q ⊗ N ⟶ P) :
    ∃! h : Q ⟶ P˜, (h ⊗ₘ 𝟙 N) ≫ app = g := by
  let equiv : (Q ⊗ N ⟶ P) ≃ (Q ⟶ P˜) := braidEquiv.trans (curryEquiv.trans transportEquiv)
  refine ⟨equiv g, ?exist, ?uniq⟩
  case exist =>
    simp only [equiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom,
      Iso.symm_inv, Category.comp_id, Category.id_comp]
    let h' := curryEquiv ((β_ N Q).hom ≫ g)
    let ev := adj.counit.app P
    have adj : (𝟙 N ⊗ₘ h') ≫ ev = (β_ N Q).hom ≫ g := by
      rw [id_tensorHom]
      change (tensorLeft N).map h' ≫ Ptilde.adj.counit.app P = (β_ N Q).hom ≫ g
      erw [← Ptilde.adj.homEquiv_symm_apply]
      exact (Ptilde.adj.homEquiv Q P).symm_apply_apply _
    change ((h' ≫ backward) ⊗ₘ 𝟙 N) ≫ app = g
    have key : ((h' ≫ backward) ⊗ₘ 𝟙 N) ≫ app = (β_ Q N).hom ≫ ((𝟙 N ⊗ₘ h') ≫ ev) :=
      calc ((h' ≫ backward) ⊗ₘ 𝟙 N) ≫ app
        _ = ((h' ≫ backward) ⊗ₘ 𝟙 N) ≫ (forward ⊗ₘ 𝟙 N) ≫ (β_ (N ⟹ P) N).hom ≫ ev := rfl
        _ = ((h' ≫ backward ⊗ₘ 𝟙 N) ≫ (forward ⊗ₘ 𝟙 N)) ≫ (β_ (N ⟹ P) N).hom ≫ ev := by
          rw [Category.assoc]
        _ = (((h' ≫ backward) ≫ forward) ⊗ₘ 𝟙 N) ≫ ((β_ (N ⟹ P) N).hom ≫ ev) := by
          rw [tensorHom_id, tensorHom_id, ← comp_whiskerRight, tensorHom_id]
        _ = ((h' ≫ 𝟙 (N ⟹ P)) ⊗ₘ 𝟙 N) ≫ ((β_ (N ⟹ P) N).hom ≫ ev) := by
          rw [Category.assoc, backward_forward]
        _ = ((h' ⊗ₘ 𝟙 N) ≫ (β_ (N ⟹ P) N).hom) ≫ ev := by
          rw [Category.comp_id, Category.assoc]
        _ = ((β_ Q N).hom ≫ (𝟙 N ⊗ₘ h')) ≫ ev :=
          congrArg (fun z => z ≫ ev) (BraidedCategory.braiding_naturality h' (𝟙 N))
        _ = (β_ Q N).hom ≫ ((𝟙 N ⊗ₘ h') ≫ ev) := by rw [Category.assoc]
    rw [key, adj]
    exact SymmetricCategory.symmetry_assoc Q N g
  case uniq =>
    intro h hh
    apply equiv.symm.injective
    rw [Equiv.symm_apply_apply]
    symm
    set_option maxRecDepth 1024 in
    calc g
      _ = (h ⊗ₘ 𝟙 N) ≫ app := hh.symm
      _ = (h ⊗ₘ 𝟙 N) ≫ ((forward ⊗ₘ 𝟙 N) ≫ (β_ (N ⟹ P) N).hom ≫ adj.counit.app P) := rfl
      _ = ((h ⊗ₘ 𝟙 N) ≫ (forward ⊗ₘ 𝟙 N)) ≫ ((β_ (N ⟹ P) N).hom ≫ adj.counit.app P) := by
        rw [Category.assoc]
      _ = ((h ≫ forward) ⊗ₘ 𝟙 N) ≫ (β_ (N ⟹ P) N).hom ≫ adj.counit.app P := by
        rw [tensorHom_id, tensorHom_id, ← comp_whiskerRight, tensorHom_id]
      _ = (β_ Q N).hom ≫ (𝟙 N ⊗ₘ (h ≫ forward)) ≫ adj.counit.app P := by
        rw [← Category.assoc, ← Category.assoc]
        rfl

end Ptilde
