module


public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Fintype

public import Catex.Lent.FinInj

@[expose] public section

open CategoryTheory Function

open FinInj

/-!
For ℓ, m, n ∈ ℕ, define the following morphisms in the category I:
• λ_{ℓ,m} : [ℓ] → [ℓ + m] given by λ_{ℓ,m}(x) = x
• ρ_{m,n} : [n] → [m + n] given by ρ_{m,n}(x) = m + x

A covariant presheaf S in Setᴵ is defined to be suitable whenever, for all ℓ, m, n ∈ ℕ,
the following commutative square in Set is a pullback:

```
       S(λ_{ℓ,m})
  S[m] ---------> S[m + n]
    |               |
    | S(ρ_{ℓ,m})    | S(ρ_{ℓ,m+n})
    v               v
  S[ℓ+m] -------> S[ℓ + m + n]
       S(λ_{ℓ+m,n})
```

Define S(I) to be the full subcategory of Setᴵ consisting of the suitable covariant presheaves.
Give a functor Setᴵ → S(I) together with a proof that it is a left adjoint to the inclusion
functor S(I) ↪ Setᴵ.
-/

@[ext]
theorem hom_ext {a b : ℕ} {f g : a ⟶ b} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

def sq₁ (ℓ m _ : ℕ) : m ⟶ ℓ + m := Fin.natAddEmb ℓ
def sq₂ (_ m n : ℕ) : m ⟶ m + n := Fin.castAddEmb n
def sq₃ (ℓ m n : ℕ) : ℓ + m ⟶ ℓ + m + n := Fin.castAddEmb n
def sq₄ (ℓ m n : ℕ) : m + n ⟶ ℓ + m + n := (Fin.natAddEmb ℓ).trans (finCongr (add_assoc ℓ m n).symm)

theorem sq_comm {ℓ m n : ℕ} : sq₁ ℓ m n ≫ sq₃ ℓ m n = sq₂ ℓ m n ≫ sq₄ ℓ m n := rfl

/--
A presheaf S is suitable if for all ℓ, m, n, the square
```
        S(𝜆ₘ,ₙ)
  S(m) ---------> S(m+n)
    |               |
    | S(ρₗ,ₘ)       | S(ρₗ,ₘ₊ₙ)
    v               v
  S(l+m) -------> S(l+m+n)
        S(𝜆ₗ₊ₘ,ₙ)
```
forms a pullback.
-/
def Suitable : ObjectProperty (ℕ ⥤ Type) :=
  fun P => ∀ ℓ m n, IsPullback
    (P.map (sq₁ ℓ m n))
    (P.map (sq₂ ℓ m n))
    (P.map (sq₃ ℓ m n))
    (P.map (sq₄ ℓ m n))

structure Raw (P : ℕ ⥤ Type) where
  k : ℕ
  s : Fin k ↪ ℕ
  x : P.obj k

noncomputable def factEmb {k m : ℕ} (s : Fin k ↪ ℕ) (t : Fin m ↪ ℕ)
    (h : ∀ i, s i ∈ Set.range t) : Fin k ↪ Fin m where
  toFun i := (Equiv.ofInjective ⇑t t.injective).symm ⟨s i, h i⟩
  inj' i j hij := s.injective (by
    have h2 := (Equiv.ofInjective ⇑t t.injective).symm.injective hij
    simpa only [Subtype.ext_iff] using h2)

@[simp] theorem factEmb_spec {k m : ℕ} (s : Fin k ↪ ℕ) (t : Fin m ↪ ℕ)
    (h : ∀ i, s i ∈ Set.range t) (i : Fin k) : t (factEmb s t h i) = s i :=
  Equiv.apply_ofInjective_symm t.injective ⟨s i, h i⟩

theorem factEmb_trans {k m : ℕ} (s : Fin k ↪ ℕ) (t : Fin m ↪ ℕ)
    (h : ∀ i, s i ∈ Set.range t) : (factEmb s t h).trans t = s := by
  ext; simp

def Glued (z w : Raw P) : Prop :=
  ∃ (m : ℕ) (u : z.k ⟶ m) (u' : w.k ⟶ m) (t : Fin m ↪ ℕ),
    z.s = u.trans t ∧
    w.s = u'.trans t ∧
    P.map u z.x = P.map u' w.x

theorem Glued.refl (z : Raw P) : Glued z z :=
  ⟨z.k, 𝟙 z.k, 𝟙 z.k, z.s, rfl, rfl, rfl⟩

theorem Glued.symm {z₁ z₂ : Raw P} : Glued z₁ z₂ → Glued z₂ z₁
  | ⟨m, u, u', t, hu, hu', hx⟩ => ⟨m, u', u, t, hu', hu, hx.symm⟩

theorem Glued.trans {z₁ z₂ z₃ : Raw P} : Glued z₁ z₂ → Glued z₂ z₃ → Glued z₁ z₃ := by
  intro ⟨m, u₁, u₂, t, h1, h2, hx⟩ ⟨m', u₂', u₃, t', h2', h3, hx'⟩
  have ⟨M, T, hTt, hTt'⟩ : ∃ (M : ℕ) (T : Fin M ↪ ℕ),
      (∀ i, t i ∈ Set.range T) ∧ (∀ i, t' i ∈ Set.range T) := by
    let F : Finset ℕ := Finset.univ.image t ∪ Finset.univ.image t'
    have hTrange : Set.range (F.orderEmbOfFin rfl).toEmbedding = F := by
      simp
    refine ⟨F.card, (F.orderEmbOfFin rfl).toEmbedding, ?_, ?_⟩
    all_goals
      intro i
      rw [hTrange]
      simp [F]
  let v : m ⟶ M := factEmb t T hTt
  let v' : m' ⟶ M := factEmb t' T hTt'
  have hvt : v.trans T = t := factEmb_trans t T hTt
  have hvt' : v'.trans T = t' := factEmb_trans t' T hTt'
  have hmid : u₂ ≫ v = u₂' ≫ v' := by
    apply hom_ext
    intro j
    apply T.injective
    have e1 : T ((u₂ ≫ v) j) = z₂.s j := by
      have hh : u₂.trans (v.trans T) j = z₂.s j := by rw [hvt, ← h2]
      rw [Embedding.trans_apply] at hh
      exact hh
    have e2 : T ((u₂' ≫ v') j) = z₂.s j := by
      have hh : u₂'.trans (v'.trans T) j = z₂.s j := by rw [hvt', ← h2']
      rw [Embedding.trans_apply] at hh
      exact hh
    rw [e1, e2]
  refine ⟨M, u₁ ≫ v, u₃ ≫ v', T, ?_, ?_, ?_⟩
  · rw [h1]
    change u₁.trans t = (u₁.trans v).trans T
    rw [Embedding.trans_assoc, hvt]
  · rw [h3]
    change u₃.trans t' = (u₃.trans v').trans T
    rw [Embedding.trans_assoc, hvt']
  · rw [Functor.map_comp, Functor.map_comp]
    change P.map v (P.map u₁ z₁.x) = P.map v' (P.map u₃ z₃.x)
    rw [hx, ← hx', ← Functor.map_comp_apply, ← Functor.map_comp_apply, hmid]

instance Raw.instSetoid (P : ℕ ⥤ Type) : Setoid (Raw P) where
  r := Glued
  iseqv := ⟨Glued.refl, Glued.symm, Glued.trans⟩

def Pω (P : ℕ ⥤ Type) : Type := Quotient (Raw.instSetoid P)

def Pω.mk (z : Raw P) : Pω P := Quotient.mk _ z

@[elab_as_elim]
theorem Pω.ind {motive : Pω P → Prop} (mk : ∀ z, motive (Pω.mk z)) :
    ∀ x, motive x := Quotient.ind mk

def Raw.smul (π : Equiv.Perm ℕ) (z : Raw P) : Raw P :=
  ⟨z.k, z.s.trans π, z.x⟩

@[simp] theorem Raw.smul_s (π : Equiv.Perm ℕ) (z : Raw P) :
    (Raw.smul π z).s = z.s.trans π := rfl

theorem Raw.smul_rel (π : Equiv.Perm ℕ) {z w : Raw P} (h : z ≈ w) :
    Raw.smul π z ≈ Raw.smul π w := by
  have ⟨m, u, u', t, hu, hu', hx⟩ := h
  refine ⟨m, u, u', t.trans π, ?_, ?_, hx⟩
  · rw [Raw.smul_s, hu]; exact Embedding.trans_assoc u t _
  · rw [Raw.smul_s, hu']; exact Embedding.trans_assoc u' t _

instance : SMul (Equiv.Perm ℕ) (Pω P) where
  smul π := Quotient.map (Raw.smul π) (fun _ _ => Raw.smul_rel π)

@[simp] theorem Pω.smul_mk (π : Equiv.Perm ℕ) (z : Raw P) :
    π • Pω.mk z = Pω.mk (Raw.smul π z) := rfl

theorem Pω.mk_map {k N : ℕ} (u : k ⟶ N) (t : Fin N ↪ ℕ) (x : P.obj k) :
    Pω.mk (⟨N, t, P.map u x⟩ : Raw P) = Pω.mk ⟨k, u.trans t, x⟩ :=
  Quotient.sound ⟨N, 𝟙 N, u, t, rfl, rfl, by simp⟩

instance : MulAction (Equiv.Perm ℕ) (Pω P) where
  one_smul := by
    intro b
    cases b using Pω.ind with | _ z =>
    have ⟨k, s, x⟩ := z
    simp only [Pω.smul_mk, Raw.smul]
    have h : s.trans (1 : Equiv.Perm ℕ) = s := by ext; simp
    rw [h]
  mul_smul π₁ π₂ := by
    intro b
    cases b using Pω.ind with | _ z =>
    have ⟨k, s, x⟩ := z
    simp only [Pω.smul_mk, Raw.smul]
    have h : s.trans (π₁ * π₂)
        = (s.trans π₂).trans π₁.toEmbedding := by
      ext; simp [Equiv.Perm.mul_apply]
    rw [h]

def Supports (A : Set ℕ) (z : Pω P) : Prop :=
  ∀ π : Equiv.Perm ℕ, (∀ a ∈ A, π a = a) → π • z = z

theorem Supports.range (z : Raw P) : Supports (Set.range z.s) (Pω.mk z) := by
  intro π hπ
  have hs : (Raw.smul π z).s = z.s := by
    ext i
    simp only [Raw.smul_s]
    exact hπ _ ⟨i, rfl⟩
  rw [Pω.smul_mk]
  exact Quotient.sound ⟨z.k, 𝟙 _, 𝟙 _, z.s, hs, rfl, rfl⟩

theorem Supports.swap_eq {A : Set ℕ} {z : Pω P} (h : Supports A z)
    {a b : ℕ} (ha : a ∉ A) (hb : b ∉ A) : Equiv.swap a b • z = z := by
  apply h
  intro x hx
  apply Equiv.swap_apply_of_ne_of_ne
  · intro rfl; exact ha hx
  · intro rfl; exact hb hx

theorem swap_fresh_aux {z : Pω P} {a b c : ℕ} (hab : a ≠ b) (hcb : c ≠ b)
    (h_ac : Equiv.swap a c • z = z) (h_cb : Equiv.swap c b • z = z) :
    Equiv.swap a b • z = z :=
  calc Equiv.swap a b • z
    _ = (Equiv.swap c a * Equiv.swap b c * Equiv.swap c a) • z := by
          rw [← Equiv.swap_mul_swap_mul_swap hcb.symm hab.symm]
    _ = (Equiv.swap a c * Equiv.swap c b * Equiv.swap a c) • z := by
          rw [Equiv.swap_comm c a, Equiv.swap_comm b c]
    _ = Equiv.swap a c • Equiv.swap c b • Equiv.swap a c • z := by rw [mul_smul, mul_smul]
    _ = Equiv.swap a c • Equiv.swap c b • z := by rw [h_ac]
    _ = Equiv.swap a c • z := by rw [h_cb]
    _ = z := by rw [h_ac]

theorem Supports.swap_fix {A B : Set ℕ} (hA : A.Finite) (hB : B.Finite) {z : Pω P}
    (ha : Supports A z) (hb : Supports B z) {a b : ℕ}
    (ha' : a ∉ A ∩ B) (hb' : b ∉ A ∩ B) : Equiv.swap a b • z = z := by
  have hS : (A ∪ B ∪ {a, b}).Finite := (hA.union hB).union (Set.toFinite _)
  have ⟨c, hc⟩ := hS.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at hc
  have ⟨⟨hcA, hcB⟩, _, hcb⟩ := hc
  by_cases haA : a ∈ A
  · have haB : a ∉ B := fun h => ha' ⟨haA, h⟩
    by_cases hbB : b ∈ B
    · have hbA : b ∉ A := fun h => hb' ⟨h, hbB⟩
      exact swap_fresh_aux (ne_of_mem_of_not_mem haA hbA) hcb
        (hb.swap_eq haB hcB) (ha.swap_eq hcA hbA)
    · exact hb.swap_eq haB hbB
  · by_cases hbA : b ∈ A
    · have hbB : b ∉ B := fun h => hb' ⟨hbA, h⟩
      by_cases haB : a ∈ B
      · exact swap_fresh_aux (ne_of_mem_of_not_mem hbA haA).symm hcb
          (ha.swap_eq haA hcA) (hb.swap_eq hcB hbB)
      · exact hb.swap_eq haB hbB
    · exact ha.swap_eq haA hbA

theorem realize {C : Set ℕ} {z : Pω P}
    (hsw : ∀ a b, a ∉ C → b ∉ C → Equiv.swap a b • z = z)
    {π : Equiv.Perm ℕ} (hπ : ∀ c ∈ C, π c = c) (D : Finset ℕ) :
    ∃ ρ : Equiv.Perm ℕ,
      ρ • z = z ∧ (∀ c ∈ C, ρ c = c) ∧ (∀ d ∈ D, ρ d = π d) := by
  induction D using Finset.induction_on with
  | empty => exact ⟨1, one_smul _ _, fun c _ => rfl, fun d hd => absurd hd (by simp)⟩
  | insert d D' hd ih =>
    have ⟨ρ', hρ'z, hρ'C, hρ'D⟩ := ih
    by_cases hfe : ρ' d = π d
    · refine ⟨ρ', hρ'z, hρ'C, ?_⟩
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact hfe
      · exact hρ'D e he'
    · have hdC : d ∉ C := fun h => hfe (by rw [hρ'C d h, hπ d h])
      have heC : π d ∉ C := fun h => hdC (π.injective (hπ (π d) h) ▸ h)
      have hfC : ρ' d ∉ C := fun h => hdC (ρ'.injective (hρ'C (ρ' d) h) ▸ h)
      refine ⟨Equiv.swap (ρ' d) (π d) * ρ', ?_, ?_, ?_⟩
      · rw [mul_smul, hρ'z, hsw _ _ hfC heC]
      · intro c hc
        rw [Equiv.Perm.mul_apply, hρ'C c hc, Equiv.swap_apply_of_ne_of_ne
          (ne_of_mem_of_not_mem hc hfC) (ne_of_mem_of_not_mem hc heC)]
      · intro e' he'
        rcases Finset.mem_insert.mp he' with rfl | he''
        · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        · rw [Equiv.Perm.mul_apply, hρ'D e' he'']
          apply Equiv.swap_apply_of_ne_of_ne
          · rw [← hρ'D e' he'']
            exact ρ'.injective.ne (ne_of_mem_of_not_mem he'' hd)
          · exact π.injective.ne (ne_of_mem_of_not_mem he'' hd)

theorem Supports.inter {A B : Set ℕ} (hA : A.Finite) (hB : B.Finite) {z : Pω P}
    (ha : Supports A z) (hb : Supports B z) : Supports (A ∩ B) z := by
  cases z using Pω.ind with | _ w =>
  intro π hπ
  have hsw : ∀ a b, a ∉ A ∩ B → b ∉ A ∩ B → Equiv.swap a b • Pω.mk w = Pω.mk w :=
    fun a b => Supports.swap_fix hA hB ha hb
  have ⟨ρ, hρz, _, hρD⟩ := realize hsw hπ (Finset.univ.image w.s)
  have hagree : ∀ i, ρ (w.s i) = π (w.s i) := fun i => hρD _ (by simp)
  have heq : π • Pω.mk w = ρ • Pω.mk w := by
    rw [Pω.smul_mk, Pω.smul_mk]
    congr 1
    have : w.s.trans π = w.s.trans ρ.toEmbedding := by
      ext i
      simp only [Embedding.trans_apply, Equiv.coe_toEmbedding]
      exact (hagree i).symm
    rw [Raw.smul, Raw.smul, this]
  rw [heq, hρz]

theorem exists_perm_eqOn (g : ℕ → ℕ) (D : Finset ℕ) (hg : Set.InjOn g ↑D) :
    ∃ ρ : Equiv.Perm ℕ, ∀ d ∈ D, ρ d = g d := by
  classical
  have : Finite {x | x ∈ (↑D : Set ℕ)} := D.finite_toSet.to_subtype
  refine ⟨(Equiv.Set.imageOfInjOn g ↑D hg).extendSubtype, fun d hd => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ d (Finset.mem_coe.mpr hd)]
  rfl

def extFun {m n : ℕ} (u : m ⟶ n) (k : ℕ) : ℕ :=
  if h : k < m then u ⟨k, h⟩ else k

theorem extPerm_exists {m n : ℕ} (u : m ⟶ n) :
    ∃ ρ : Equiv.Perm ℕ, ∀ d ∈ Finset.range m, ρ d = extFun u d := by
  apply exists_perm_eqOn (extFun u) (Finset.range m)
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only [extFun, dif_pos ha, dif_pos hb] at hab
  simpa using u.injective (Fin.val_injective hab)

noncomputable def extPerm {m n : ℕ} (u : m ⟶ n) : Equiv.Perm ℕ := (extPerm_exists u).choose

theorem extPerm_apply {m n : ℕ} (u : m ⟶ n) (i : Fin m) :
    extPerm u i = u i := by
  have h := (extPerm_exists u).choose_spec i (Finset.mem_range.mpr i.isLt)
  change (extPerm_exists u).choose i = u i
  rw [h, extFun, dif_pos i.isLt]

theorem extPerm_lt {m n : ℕ} (u : m ⟶ n) {k : ℕ} (hk : k < m) : extPerm u k < n := by
  have h : extPerm u (⟨k, hk⟩ : Fin m) = u ⟨k, hk⟩ := extPerm_apply u ⟨k, hk⟩
  rw [h]
  exact (u ⟨k, hk⟩).isLt

theorem Supports.smul_eq_of_eqOn {n : ℕ} {z : Pω P} (hz : Supports {a | a < n} z)
    {p q : Equiv.Perm ℕ} (h : ∀ a, a < n → p a = q a) : p • z = q • z := by
  have hfix : (q⁻¹ * p) • z = z := by
    apply hz
    intro a ha
    rw [Set.mem_setOf_eq] at ha
    rw [Equiv.Perm.mul_apply, h a ha]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  calc p • z
    _ = q • ((q⁻¹ * p) • z) := by rw [← mul_smul, mul_inv_cancel_left]
    _ = q • z := by rw [hfix]

theorem extPerm_apply_lt {m n : ℕ} (u : m ⟶ n) {k : ℕ} (hk : k < m) :
    extPerm u k = u ⟨k, hk⟩ := by
  simpa using extPerm_apply u ⟨k, hk⟩

theorem supports_extPerm {m n : ℕ} (u : m ⟶ n) {z : Pω P}
    (hz : Supports {a | a < m} z) : Supports {a | a < n} (extPerm u • z) := by
  intro σ hσ
  have hfix : ((extPerm u)⁻¹ * σ * extPerm u) • z = z := hz _ (by
    intro a ha
    rw [Set.mem_setOf_eq] at ha
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ _ (extPerm_lt u ha)]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl)
  have key : σ * extPerm u = extPerm u * ((extPerm u)⁻¹ * σ * extPerm u) := by
    rw [mul_assoc (extPerm u)⁻¹ σ, mul_inv_cancel_left]
  rw [← mul_smul, key, mul_smul, hfix]

theorem Supports.mono {A B : Set ℕ} {z : Pω P} (hAB : A ⊆ B) (h : Supports A z) :
    Supports B z := fun π hπ => h π fun a ha => hπ a (hAB ha)

theorem Supports.smul {A : Set ℕ} {z : Pω P} (h : Supports A z) (p : Equiv.Perm ℕ) :
    Supports (p '' A) (p • z) := by
  intro σ hσ
  have hfix : (p⁻¹ * σ * p) • z = z := h _ (by
    intro a ha
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ (p a) ⟨a, ha, rfl⟩]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl)
  have key : σ * p = p * (p⁻¹ * σ * p) := by rw [mul_assoc p⁻¹ σ, mul_inv_cancel_left]
  rw [← mul_smul, key, mul_smul, hfix]

theorem extPerm_sq₁ {ℓ m n k : ℕ} (hk : k < m) : extPerm (sq₁ ℓ m n) k = ℓ + k := by
  rw [extPerm_apply_lt _ hk]; rfl

theorem extPerm_sq₂ {ℓ m n k : ℕ} (hk : k < m) : extPerm (sq₂ ℓ m n) k = k := by
  rw [extPerm_apply_lt _ hk]; rfl

theorem extPerm_sq₃ {ℓ m n k : ℕ} (hk : k < ℓ + m) : extPerm (sq₃ ℓ m n) k = k := by
  rw [extPerm_apply_lt _ hk]; rfl

theorem extPerm_sq₄ {ℓ m n k : ℕ} (hk : k < m + n) : extPerm (sq₄ ℓ m n) k = ℓ + k := by
  rw [extPerm_apply_lt _ hk]; rfl

abbrev L.obj (P : ℕ ⥤ Type) (n : ℕ) : Type := { z : Pω P // Supports {a | a < n} z }

noncomputable def L.map {m n : ℕ} (u : m ⟶ n) : L.obj P m → L.obj P n
  | ⟨z, hz⟩ => ⟨extPerm u • z, supports_extPerm u hz⟩

noncomputable def L.pre (P : ℕ ⥤ Type) : ℕ ⥤ Type where
  obj := L.obj P
  map u := ↾L.map u
  map_id n := by
    ext ⟨z, hz⟩
    change extPerm (𝟙 n) • z = z
    rw [Supports.smul_eq_of_eqOn hz (q := 1) (by
      intro a ha
      rw [Equiv.Perm.one_apply, extPerm_apply_lt (𝟙 n) ha]
      rfl), one_smul]
  map_comp u v := by
    ext ⟨z, hz⟩
    change extPerm (u ≫ v) • z = extPerm v • (extPerm u • z)
    rw [← mul_smul, Supports.smul_eq_of_eqOn hz (by
      intro a ha
      rw [Equiv.Perm.mul_apply, extPerm_apply_lt u ha,
        extPerm_apply_lt v (u ⟨a, ha⟩).isLt, extPerm_apply_lt (u ≫ v) ha]
      rfl)]

@[simp] theorem L.pre_map_val {m n : ℕ} (u : m ⟶ n) (x : L.obj P m) :
    ((L.pre P).map u x).val = extPerm u • x.val := rfl

theorem sq₂_smul {ℓ m n : ℕ} {z : Pω P} (hz : Supports {a | a < m} z) :
    extPerm (sq₂ ℓ m n) • z = z := by
  rw [Supports.smul_eq_of_eqOn hz (q := 1) (by
    intro a ha
    rw [extPerm_sq₂ ha, Equiv.Perm.one_apply]), one_smul]

theorem sq₃_smul {ℓ m n : ℕ} {z : Pω P} (hz : Supports {a | a < ℓ + m} z) :
    extPerm (sq₃ ℓ m n) • z = z := by
  rw [Supports.smul_eq_of_eqOn hz (q := 1) (by
    intro a ha
    rw [extPerm_sq₃ ha, Equiv.Perm.one_apply]), one_smul]

theorem L.pre_suitable (P : ℕ ⥤ Type) : Suitable (L.pre P) := by
  intro ℓ m n
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp, sq_comm]
  · intro ⟨x, hx⟩ ⟨x', hx'⟩ ⟨_, hxx⟩
    apply Subtype.ext
    have := congrArg Subtype.val hxx
    rwa [L.pre_map_val, L.pre_map_val, sq₂_smul hx, sq₂_smul hx'] at this
  · intro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ hfib
    have hfib' : extPerm (sq₃ ℓ m n) • z₁ = extPerm (sq₄ ℓ m n) • z₂ :=
      congrArg Subtype.val hfib
    rw [sq₃_smul hz₁] at hfib'
    have hwB : Supports (extPerm (sq₄ ℓ m n) '' {a | a < m + n}) z₁ := by
      rw [hfib']; exact hz₂.smul _
    have hwAB : Supports ({a | a < ℓ + m} ∩ extPerm (sq₄ ℓ m n) '' {a | a < m + n}) z₁ :=
      Supports.inter (Set.finite_lt_nat _) (Set.Finite.image _ (Set.finite_lt_nat _))
        hz₁ hwB
    have hz₂m : Supports {a | a < m} z₂ := by
      have hz₂eq : z₂ = (extPerm (sq₄ ℓ m n))⁻¹ • z₁ := by
        rw [hfib', inv_smul_smul]
      rw [hz₂eq]
      refine Supports.mono ?_ (hwAB.smul (extPerm (sq₄ ℓ m n))⁻¹)
      intro b ⟨c, ⟨hc1, d, hd, hdc⟩, hcb⟩
      simp only [Set.mem_setOf_eq] at hc1 hd ⊢
      have he : extPerm (sq₄ ℓ m n) d = ℓ + d := extPerm_sq₄ hd
      have hbd : b = d := by
        rw [← hcb, ← hdc]; exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
      omega
    refine ⟨⟨z₂, hz₂m⟩, ?_, ?_⟩
    · apply Subtype.ext
      change extPerm (sq₁ ℓ m n) • z₂ = z₁
      rw [hfib']
      refine Supports.smul_eq_of_eqOn hz₂m ?_
      intro a ha
      rw [extPerm_sq₁ ha, extPerm_sq₄ (by omega)]
    · apply Subtype.ext
      exact sq₂_smul hz₂m

def Raw.map (f : P ⟶ Q) (z : Raw P) : Raw Q := ⟨z.k, z.s, f.app z.k z.x⟩

theorem Raw.map_rel (f : P ⟶ Q) {z w : Raw P} (h : z ≈ w) : Raw.map f z ≈ Raw.map f w := by
  have ⟨m, u, u', t, hu, hu', hx⟩ := h
  refine ⟨m, u, u', t, hu, hu', ?_⟩
  change Q.map u (f.app z.k z.x) = Q.map u' (f.app w.k w.x)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hx]

def Pω.map (f : P ⟶ Q) : Pω P → Pω Q := Quotient.map (Raw.map f) (fun _ _ h => Raw.map_rel f h)

@[simp] theorem Pω.map_mk (f : P ⟶ Q) (z : Raw P) : Pω.map f (Pω.mk z) = Pω.mk (Raw.map f z) := rfl

theorem Pω.map_smul (f : P ⟶ Q) (π : Equiv.Perm ℕ) (z : Pω P) :
    Pω.map f (π • z) = π • Pω.map f z :=
  Pω.ind (fun _ => rfl) z

theorem Supports.map {A : Set ℕ} (f : P ⟶ Q) {z : Pω P} (h : Supports A z) :
    Supports A (Pω.map f z) := by
  intro π hπ
  rw [← Pω.map_smul, h π hπ]

def L.mapF {n : ℕ} (f : P ⟶ Q) : L.obj P n → L.obj Q n
  | ⟨z, hz⟩ => ⟨Pω.map f z, hz.map f⟩

def L.preMap (f : P ⟶ Q) : L.pre P ⟶ L.pre Q where
  app n := ↾L.mapF f
  naturality {m n} u := by
    ext ⟨z, hz⟩
    exact Subtype.ext (Pω.map_smul f (extPerm u) z)

theorem range_valEmbedding (n : ℕ) : Set.range (@Fin.valEmbedding n) = {a | a < n} := by
  ext a
  simp only [Set.mem_range, Set.mem_setOf_eq]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ i.isLt, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def unitApp (P : ℕ ⥤ Type) (n : ℕ) (x : P.obj n) : L.obj P n :=
  ⟨Pω.mk ⟨n, Fin.valEmbedding, x⟩, range_valEmbedding n ▸ Supports.range ⟨n, Fin.valEmbedding, x⟩⟩

theorem Raw.map_id (w : Raw P) : Raw.map (𝟙 P) w = w := by
  have ⟨k, s, x⟩ := w
  simp only [Raw.map, NatTrans.id_app, types_id_apply]

theorem Pω.map_id (z : Pω P) : Pω.map (𝟙 P) z = z := by
  cases z using Pω.ind with | _ w => rw [Pω.map_mk, Raw.map_id]

variable {R : ℕ ⥤ Type}

theorem Pω.map_comp (f : P ⟶ Q) (g : Q ⟶ R) (z : Pω P) :
    Pω.map (f ≫ g) z = Pω.map g (Pω.map f z) :=
  Pω.ind (fun _ => rfl) z

noncomputable def L : (ℕ ⥤ Type) ⥤ Suitable.FullSubcategory where
  obj P := ⟨L.pre P, L.pre_suitable P⟩
  map f := ObjectProperty.homMk (L.preMap f)
  map_id P := by ext n ⟨z, hz⟩; exact Subtype.ext (Pω.map_id z)
  map_comp f g := by ext n ⟨z, hz⟩; exact Subtype.ext (Pω.map_comp f g z)

def unit (P : ℕ ⥤ Type) : P ⟶ L.pre P where
  app n := ↾unitApp P n
  naturality {m n} u := by
    ext x
    apply Subtype.ext
    change Pω.mk ⟨n, Fin.valEmbedding, P.map u x⟩ = extPerm u • Pω.mk ⟨m, Fin.valEmbedding, x⟩
    rw [Pω.smul_mk]
    refine Quotient.sound ⟨n, 𝟙 n, u, Fin.valEmbedding, rfl, ?_, ?_⟩
    · ext i
      change extPerm u i = Fin.valEmbedding (u i)
      rw [extPerm_apply]
      rfl
    · simp only [CategoryTheory.Functor.map_id]
      rfl

theorem Suitable.map_injective_sq₂ {S : ℕ ⥤ Type} (hS : Suitable S) (m n : ℕ) :
    Injective (S.map (sq₂ n m n)) := by
  intro x x' hxx
  have hsq : sq₁ n m n = sq₂ n m n ≫ finAddFlip.toEmbedding :=
    hom_ext fun i => (finAddFlip_apply_castAdd i n).symm
  refine Limits.Types.ext_of_isPullback (hS n m n) ?_ hxx
  rw [hsq, S.map_comp, types_comp_apply, types_comp_apply, hxx]

variable {S : ℕ ⥤ Type}

theorem map_injective_of_comp_id {a b : ℕ} (u : a ⟶ b) (w : b ⟶ a) (h : u ≫ w = 𝟙 a) :
    Injective (S.map u) :=
  have hlin : Function.LeftInverse (S.map w) (S.map u) := fun x => by
    rw [← types_comp_apply, ← S.map_comp, h, S.map_id, types_id_apply]
  hlin.injective

theorem Suitable.map_injective (hS : Suitable S) {a b : ℕ} (u : a ⟶ b) : Injective (S.map u) := by
  have hab : a ≤ b := FinInj.le u
  have heq : a + (b - a) = b := Nat.add_sub_cancel' hab
  have ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE hab) u (Fin.castLE_injective hab) u.injective
  let σhom : b ⟶ b := σ.toEmbedding
  let chom : a + (b - a) ⟶ b := (finCongr heq).toEmbedding
  have hu : u = (sq₂ 0 a (b - a) ≫ chom) ≫ σhom := by
    apply hom_ext; intro i
    change u i = σhom (chom (sq₂ 0 a (b - a) i))
    have harg : chom (sq₂ 0 a (b - a) i) = (⟨i, by omega⟩ : Fin b) := Fin.ext rfl
    rw [harg]
    exact (hσ i).symm
  rw [hu, S.map_comp, S.map_comp, types_comp, types_comp]
  refine (map_injective_of_comp_id σhom σ.symm.toEmbedding ?_).comp
    ((map_injective_of_comp_id chom (finCongr heq).symm.toEmbedding ?_).comp
      (hS.map_injective_sq₂ a (b - a)))
  · exact hom_ext fun i => σ.symm_apply_apply i
  · exact hom_ext fun i => (finCongr heq).symm_apply_apply i

theorem Suitable.colim_inj (hS : Suitable S) {K : ℕ} (t : Fin K ↪ ℕ) {x x' : S.obj K}
    (h : Pω.mk (⟨K, t, x⟩ : Raw S) = Pω.mk ⟨K, t, x'⟩) : x = x' := by
  have ⟨M, u, u', τ, hu, hu', hval⟩ := Quotient.exact h
  have huu : u = u' := by
    apply hom_ext; intro i
    apply τ.injective
    have e : u.trans τ i = u'.trans τ i := by rw [← hu, ← hu']
    simpa only [Embedding.trans_apply] using e
  rw [huu] at hval
  exact Suitable.map_injective hS u' hval

theorem unit_inj (hS : Suitable S) (n : ℕ) : Injective (unitApp S n) :=
  fun _ _ hxx => Suitable.colim_inj hS Fin.valEmbedding (congrArg Subtype.val hxx)

theorem relabel {k : ℕ} (s : Fin k ↪ ℕ) (x : S.obj k) (ζ ζ' : k ⟶ k) (hζ : ζ' ≫ ζ = 𝟙 k) :
    Pω.mk (⟨k, ζ.trans s, S.map ζ' x⟩ : Raw S) = Pω.mk ⟨k, s, x⟩ := by
  refine Quotient.sound ⟨k, ζ, 𝟙 k, s, rfl, rfl, ?_⟩
  change S.map ζ (S.map ζ' x) = S.map (𝟙 k) x
  rw [← types_comp_apply, ← S.map_comp, hζ]

def swapHom {k : ℕ} (i j : Fin k) : k ⟶ k := (Equiv.swap i j).toEmbedding

theorem swapHom_comp_self {k : ℕ} (i j : Fin k) : swapHom i j ≫ swapHom i j = 𝟙 k :=
  hom_ext fun a => Equiv.swap_apply_self i j a

def cyc (k' : ℕ) : k' + 1 ⟶ 1 + k' := finAddFlip.toEmbedding

theorem cyc_lt {k' : ℕ} (i : Fin (k' + 1)) (h : i < k') : (cyc k' i : ℕ) = 1 + i :=
  congrArg Fin.val (finAddFlip_apply_mk_left h)

theorem cyc_ge {k' : ℕ} (i : Fin (k' + 1)) (h : ¬i < k') : (cyc k' i : ℕ) = 0 := by
  have e : (cyc k' i : ℕ) = (i : ℕ) - k' :=
    congrArg Fin.val (finAddFlip_apply_mk_right (not_lt.mp h) i.isLt)
  omega

theorem remove_last (hS : Suitable S) {n k' : ℕ} (s : Fin (k' + 1) ↪ ℕ) (x : S.obj (k' + 1))
    (hsupp : Supports {a | a < n} (Pω.mk ⟨k' + 1, s, x⟩))
    (hbad : n ≤ s ⟨k', Nat.lt_succ_self k'⟩) :
    ∃ (s' : Fin k' ↪ ℕ) (y : S.obj k'),
      Pω.mk (⟨k', s', y⟩ : Raw S) = Pω.mk ⟨k' + 1, s, x⟩ := by
  have ⟨c, hc⟩ := ((Set.finite_range s).union (Set.finite_lt_nat n)).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_range, Set.mem_setOf_eq, not_or,
    not_exists] at hc
  have ⟨hcs, hcn⟩ := hc
  rw [not_lt] at hcn
  let t : Fin (1 + k' + 1) ↪ ℕ :=
    ⟨fun j : Fin (1 + k' + 1) => if (j : ℕ) = 0 then c else s ⟨(j : ℕ) - 1, by omega⟩, by
      intro j₁ j₂ hij
      by_cases h1 : (j₁ : ℕ) = 0 <;>
      by_cases h2 : (j₂ : ℕ) = 0 <;>
        simp only [h1, h2, if_true, if_false] at hij
      · exact Fin.ext (by omega)
      · exact absurd hij.symm (hcs _)
      · exact absurd hij (hcs _)
      · have h3 := s.injective hij
        simp only [Fin.ext_iff] at h3
        exact Fin.ext (by omega)⟩
  have hts : ∀ i : Fin (k' + 1), t ⟨1 + i, by omega⟩ = s i := by
    intro i
    have hi : (⟨(1 + (i : ℕ)) - 1, by omega⟩ : Fin (k' + 1)) = i := by
      apply Fin.ext
      rw [Fin.val_mk]
      omega
    change (if (1 + (i : ℕ)) = 0 then c else s ⟨(1 + i) - 1, by omega⟩) = s i
    rw [if_neg (by omega), hi]
  let u₀ : k' + 1 ⟶ 1 + k' + 1 := sq₄ 1 k' 1
  let u₁ : k' + 1 ⟶ 1 + k' + 1 := cyc k' ≫ sq₃ 1 k' 1
  have hu0t : u₀.trans t = s := by
    ext i
    change t (⟨1 + (i : ℕ), _⟩) = s i
    rw [hts i]
  have hu1t : u₁.trans t = s.trans (Equiv.swap (s ⟨k', Nat.lt_succ_self k'⟩) c) := by
    ext i
    change t (u₁ i) = Equiv.swap (s ⟨k', Nat.lt_succ_self k'⟩) c (s i)
    have hval : (u₁ i : ℕ) = cyc k' i := rfl
    by_cases h : i < k'
    · have e1 : u₁ i = (⟨1 + i, by omega⟩ : Fin (1 + k' + 1)) := by
        apply Fin.ext; rw [hval, cyc_lt i h]
      rw [e1, hts i, Equiv.swap_apply_of_ne_of_ne]
      · intro heq
        have := Fin.ext_iff.mp (s.injective heq)
        dsimp only at this
        omega
      · exact hcs i
    · have e0 : u₁ i = (⟨0, by omega⟩ : Fin (1 + k' + 1)) := by
        apply Fin.ext; rw [hval, cyc_ge i h]
      have hsi : s i = s ⟨k', Nat.lt_succ_self k'⟩ := by
        congr 1
        apply Fin.ext
        dsimp only
        omega
      rw [e0, hsi, Equiv.swap_apply_left]
      rfl
  have rep0 : Pω.mk (⟨1 + k' + 1, t, S.map u₀ x⟩ : Raw S) = Pω.mk ⟨k' + 1, s, x⟩ := by
    rw [Pω.mk_map u₀ t x, hu0t]
  have rep1 : Pω.mk (⟨1 + k' + 1, t, S.map u₁ x⟩ : Raw S)
      = Pω.mk ⟨k' + 1, s.trans (Equiv.swap (s ⟨k', Nat.lt_succ_self k'⟩) c), x⟩ := by
    rw [Pω.mk_map u₁ t x, hu1t]
  have hsw : Pω.mk (⟨k' + 1, s.trans (Equiv.swap (s ⟨k', Nat.lt_succ_self k'⟩) c), x⟩
      : Raw S) = Pω.mk ⟨k' + 1, s, x⟩ := by
    have hfix := hsupp (Equiv.swap (s ⟨k', Nat.lt_succ_self k'⟩) c) (by
      intro a ha
      rw [Set.mem_setOf_eq] at ha
      apply Equiv.swap_apply_of_ne_of_ne <;> omega)
    rwa [Pω.smul_mk] at hfix
  have hu01 : S.map u₀ x = S.map u₁ x := Suitable.colim_inj hS t (by rw [rep0, rep1, hsw])
  have hpf : S.map (sq₃ 1 k' 1) (S.map (cyc k') x) = S.map (sq₄ 1 k' 1) x := by
    rw [← types_comp_apply (S.map (cyc k')) (S.map (sq₃ 1 k' 1)), ← S.map_comp]
    exact hu01.symm
  have ⟨w, _, hwx⟩ := Limits.Types.exists_of_isPullback (hS 1 k' 1) (S.map (cyc k') x) x hpf
  exact ⟨(sq₂ 1 k' 1).trans s, w, hwx ▸ (Pω.mk_map (sq₂ 1 k' 1) s w).symm⟩

theorem mem_range_unit_of_le {k n : ℕ} (s : Fin k ↪ ℕ) (x : S.obj k)
    (hsn : ∀ i, s i < n)
    (hz : Supports {a | a < n} (Pω.mk ⟨k, s, x⟩)) :
    ∃ w, unitApp S n w = ⟨Pω.mk ⟨k, s, x⟩, hz⟩ := by
  let u : k ⟶ n := ⟨fun i => ⟨s i, hsn i⟩, fun i j hij => s.injective (Fin.ext_iff.mp hij)⟩
  exact ⟨S.map u x, Subtype.ext (Pω.mk_map u Fin.valEmbedding x)⟩

theorem key_surj (hS : Suitable S) (n : ℕ) (z : Raw S)
    (hz : Supports {a | a < n} (Pω.mk z)) :
    ∃ w : S.obj n, Pω.mk (⟨n, Fin.valEmbedding, w⟩ : Raw S) = Pω.mk z := by
  have ⟨k, s, x⟩ := z
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hall : ∀ i, s i < n
    · have ⟨w, hw⟩ := mem_range_unit_of_le s x hall hz
      exact ⟨w, congrArg Subtype.val hw⟩
    · simp only [not_forall, not_lt] at hall
      have ⟨i₀, hi₀⟩ := hall
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
        ⟨k - 1, by have := i₀.isLt; omega⟩
      let ζ : k' + 1 ⟶ k' + 1 := swapHom i₀ ⟨k', Nat.lt_succ_self k'⟩
      have hrelabel := relabel s x ζ ζ (swapHom_comp_self i₀ ⟨k', Nat.lt_succ_self k'⟩)
      let s₁ : Fin (k' + 1) ↪ ℕ := ζ.trans s
      let x₁ : S.obj (k' + 1) := S.map ζ x
      have hz₁ : Supports {a | a < n} (Pω.mk ⟨k' + 1, s₁, x₁⟩) := by rw [hrelabel]; exact hz
      have hbad : n ≤ s₁ ⟨k', Nat.lt_succ_self k'⟩ := by
        change n ≤ s (Equiv.swap i₀ ⟨k', Nat.lt_succ_self k'⟩ ⟨k', Nat.lt_succ_self k'⟩)
        rw [Equiv.swap_apply_right]
        exact hi₀
      have ⟨s', y, hrep⟩ := remove_last hS s₁ x₁ hz₁ hbad
      have hz' : Supports {a | a < n} (Pω.mk ⟨k', s', y⟩) := by rw [hrep, hrelabel]; exact hz
      have ⟨w, hw⟩ := ih k' (Nat.lt_succ_self k') s' y hz'
      exact ⟨w, by rw [hw, hrep, hrelabel]⟩

theorem unit_surj (hS : Suitable S) (n : ℕ) : Surjective (unitApp S n) := by
  intro ⟨z, hz⟩
  cases z using Pω.ind with | _ r =>
  have ⟨w, hw⟩ := key_surj hS n r hz
  exact ⟨w, Subtype.ext hw⟩

theorem unit_bij (hS : Suitable S) (n : ℕ) : Bijective (unitApp S n) :=
  ⟨unit_inj hS n, unit_surj hS n⟩

noncomputable def unitEquiv (hS : Suitable S) (n : ℕ) : S.obj n ≃ L.obj S n :=
  Equiv.ofBijective (unitApp S n) (unit_bij hS n)

@[simp] theorem unitEquiv_apply (hS : Suitable S) (n : ℕ) (x : S.obj n) :
    unitEquiv hS n x = unitApp S n x := rfl

variable {X : ℕ ⥤ Type} {Y : Suitable.FullSubcategory}

noncomputable def desc (f : X ⟶ Y.obj) : L.pre X ⟶ Y.obj where
  app n := ↾fun z => (unitEquiv Y.property n).symm (L.mapF f z)
  naturality {m n} u := by
    ext z
    change (unitEquiv Y.property n).symm (L.mapF f (L.map u z))
      = Y.obj.map u ((unitEquiv Y.property m).symm (L.mapF f z))
    apply (unitEquiv Y.property n).injective
    rw [Equiv.apply_symm_apply]
    have key : unitApp Y.obj n (Y.obj.map u ((unitEquiv Y.property m).symm (L.mapF f z)))
        = (L.pre Y.obj).map u (unitApp Y.obj m ((unitEquiv Y.property m).symm (L.mapF f z))) :=
      NatTrans.naturality_apply (unit Y.obj) u _
    rw [unitEquiv_apply, key, ← unitEquiv_apply Y.property m, Equiv.apply_symm_apply]
    exact NatTrans.naturality_apply (L.preMap f) u z

theorem unit_comp_desc (f : X ⟶ Y.obj) : unit X ≫ desc f = f := by
  ext n x
  change (unitEquiv Y.property n).symm (unitApp Y.obj n (f.app n x)) = f.app n x
  rw [← unitEquiv_apply Y.property n, Equiv.symm_apply_apply]

theorem desc_comp_unit (g : L.pre X ⟶ Y.obj) : desc (unit X ≫ g) = g := by
  ext n z
  change (unitEquiv Y.property n).symm (L.mapF (unit X ≫ g) z) = g.app n z
  apply (unitEquiv Y.property n).injective
  rw [Equiv.apply_symm_apply, unitEquiv_apply]
  apply Subtype.ext
  change Pω.map (unit X ≫ g) z.val = Pω.mk ⟨n, Fin.valEmbedding, g.app n z⟩
  have ⟨⟨k, s', x'⟩, hz1⟩ := Quotient.exists_rep z.val
  change Pω.mk ⟨k, s', x'⟩ = z.val at hz1
  have ⟨N, hnN, hsN⟩ : ∃ N, n ≤ N ∧ ∀ i, s' i < N := by
    refine ⟨n + Finset.univ.sup s' + 1, by omega, fun i => ?_⟩
    have := Finset.le_sup (f := s') (Finset.mem_univ i)
    omega
  let vN : k ⟶ N := ⟨fun i => (⟨s' i, hsN i⟩ : Fin N), fun i j hij =>
    s'.injective (Fin.ext_iff.mp hij)⟩
  have hvN : ∀ i : Fin k, extPerm vN i = s' i := by
    intro i
    rw [extPerm_apply_lt vN i.isLt]
    rfl
  have hincl : ∀ a, a < n → extPerm (Fin.castLEEmb hnN) a = a := by
    intro a ha
    rw [extPerm_apply_lt (Fin.castLEEmb hnN) ha]
    rfl
  have zN_eq : (L.pre X).map (Fin.castLEEmb hnN) z = (L.pre X).map vN (unitApp X k x') := by
    apply Subtype.ext
    change extPerm (Fin.castLEEmb hnN) • z.val = extPerm vN • Pω.mk ⟨k, Fin.valEmbedding, x'⟩
    rw [z.property (extPerm (Fin.castLEEmb hnN)) (fun a ha => hincl a ha), Pω.smul_mk, ← hz1]
    refine Quotient.sound ⟨k, 𝟙 k, 𝟙 k, s', rfl, ?_, rfl⟩
    · ext i
      exact hvN i
  have hstar : Y.obj.map (Fin.castLEEmb hnN) (g.app n z)
      = Y.obj.map vN (g.app k (unitApp X k x')) := by
    rw [← NatTrans.naturality_apply g (Fin.castLEEmb hnN) z,
      ← NatTrans.naturality_apply g vN (unitApp X k x'), zN_eq]
  have push_incl : Pω.mk (⟨n, Fin.valEmbedding, g.app n z⟩ : Raw Y.obj)
      = Pω.mk ⟨N, Fin.valEmbedding, Y.obj.map (Fin.castLEEmb hnN) (g.app n z)⟩ :=
    (Pω.mk_map (Fin.castLEEmb hnN) Fin.valEmbedding (g.app n z)).symm
  have pull_v : Pω.mk (⟨k, s', g.app k (unitApp X k x')⟩ : Raw Y.obj)
      = Pω.mk ⟨N, Fin.valEmbedding, Y.obj.map vN (g.app k (unitApp X k x'))⟩ :=
    (Pω.mk_map vN Fin.valEmbedding (g.app k (unitApp X k x'))).symm
  rw [← hz1, Pω.map_mk]
  change Pω.mk ⟨k, s', g.app k (unitApp X k x')⟩ = _
  rw [pull_v, ← hstar, ← push_incl]

theorem desc_naturality {X' : ℕ ⥤ Type} (f : X' ⟶ X) (g : X ⟶ Y.obj) :
    desc (f ≫ g) = L.preMap f ≫ desc g := by
  ext n z
  change (unitEquiv Y.property n).symm (L.mapF (f ≫ g) z)
    = (unitEquiv Y.property n).symm (L.mapF g (L.mapF f z))
  congr 1
  exact Subtype.ext (Pω.map_comp f g z.val)

noncomputable def adjunction : L ⊣ Suitable.ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun g := unit X ≫ g.hom
          invFun f := ObjectProperty.homMk (desc f)
          left_inv g := InducedCategory.hom_ext (desc_comp_unit g.hom)
          right_inv := unit_comp_desc }
      homEquiv_naturality_left_symm f g :=
        InducedCategory.hom_ext (desc_naturality f g) }
