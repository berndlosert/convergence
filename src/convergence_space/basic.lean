import tactic
import order.filter.partial
import order.filter.ultrafilter
import order.filter.bases
import algebra.support
import category_theory.concrete_category.bundled

noncomputable theory
open set function filter classical option category_theory
open_locale classical filter

variables {α β γ : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

/-- Instances of this class will be refered to as convergence structures. -/
@[ext] class convergence_space (α : Type*) :=
(converges : filter α → α → Prop)
(pure_converges : ∀ x, converges (pure x) x)
(le_converges : ∀ {l l'}, l ≤ l' → ∀ {x}, converges l' x → converges l x)

open convergence_space

section
variables (p : convergence_space α)
def converges_ (l : filter α) (x : α) : Prop := @converges _ p l x
def pure_converges_ (x : α) : converges (pure x) x := @pure_converges _ p x
def le_converges_ ⦃l l' : filter α⦄ (h : l ≤ l') {x : α} (h' : converges l' x) : converges l x
:= @le_converges _ p _ _ h _ h'
end

theorem convergence_space_eq_iff {p q : convergence_space α} :
p = q ↔ ∀ l x, @converges _ p l x ↔ @converges _ q l x :=
by simp [funext_iff, convergence_space.ext_iff p q]

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space α) := {
  le := λ p q, ∀ {l} {x}, @converges _ p l x → @converges _ q l x
}

instance : partial_order (convergence_space α) := {
  le_refl := begin
    assume p : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ p l x,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space α,
    assume h₁ : p ≤ q,
    assume h₂ : q ≤ r,
    assume l : filter α,
    assume x : α,
    assume h : converges_ p l x,
    exact (h₂ (h₁ h))
  end,
  le_antisymm := begin
    assume p q : convergence_space α,
    assume h₁ : p ≤ q,
    assume h₂ : q ≤ p,
    ext l x,
    exact iff.intro h₁ h₂,
  end,
  ..convergence_space.has_le
}

-------------------------------------------------------------------------------
-- Discrete/indiscrete convergence spaces
-------------------------------------------------------------------------------

/-- The indiscrete convergence structure is the one where every filter
 -- converges to every point. -/
def indiscrete : convergence_space α := {
  converges := λ l x, true,
  pure_converges := by tauto,
  le_converges := by tauto,
}

instance : has_top (convergence_space α) := {
  top := indiscrete
}

/-- The discrete convergence structure is the one where the only proper filters
 -- that converge are the `pure` ones. -/
def discrete : convergence_space α := {
  converges := λ l x, l ≤ pure x,
  pure_converges := by tauto,
  le_converges := by tauto,
}

instance : has_bot (convergence_space α) := {
  bot := discrete
}

-------------------------------------------------------------------------------
-- Infimum and supremum of convergence spaces
-------------------------------------------------------------------------------

instance : has_inf (convergence_space α) := {
  inf := λ p q, {
    converges := fun l x, and (converges_ p l x) (converges_ q l x),
    pure_converges := begin
      assume x : α,
      exact and.intro (pure_converges_ p x) (pure_converges_ q x),
    end,
    le_converges := begin
      assume l l' : filter α,
      assume h : l ≤ l',
      assume x : α,
      assume h' : and (converges_ p l' x) (converges_ q l' x),
      exact and.intro (le_converges_ p h h'.left) (le_converges_ q h h'.right)
    end,
  }
}

instance : has_Inf (convergence_space α) := {
  Inf := λ ps, {
    converges := λ l x, ∀ {p : convergence_space α}, p ∈ ps → converges_ p l x,
    pure_converges := begin
      assume x : α,
      assume p : convergence_space α,
      assume : p ∈ ps,
      exact pure_converges_ p x,
    end,
    le_converges := begin
      assume l l' : filter α,
      assume h : l ≤ l',
      assume x : α,
      assume f : ∀ {p : convergence_space α}, p ∈ ps → converges_ p l' x,
      assume p : convergence_space α,
      assume h' : p ∈ ps,
      exact le_converges_ p h (f h')
    end,
  }
}

instance : has_sup (convergence_space α) := {
  sup := λ p q, {
    converges := λ l x, or (converges_ p l x) (converges_ q l x),
    pure_converges := begin
      assume x : α,
      exact or.inl (pure_converges_ p x),
    end,
    le_converges := begin
      assume l l' : filter α,
      assume h : l ≤ l',
      assume x : α,
      assume h' : or (converges_ p l' x) (converges_ q l' x),
      exact or.elim h'
        (assume hl, or.inl (le_converges_ p h hl))
        (assume hr, or.inr (le_converges_ q h hr))
    end,
  }
}

instance : has_Sup (convergence_space α) := {
  Sup := λ ps, {
    converges := λ l x, or
      (l ≤ pure x)
      (∃ p : convergence_space α, p ∈ ps ∧ converges_ p l x),
    pure_converges := by tauto,
    le_converges := begin
      assume l l' : filter α,
      assume h₁ : l ≤ l',
      assume x : α,
      assume h : or
        (l' ≤ pure x)
        (∃ p : convergence_space α, p ∈ ps ∧ converges_ p l' x),
      cases h,
        case or.inl : h₂ begin
          exact or.inl (le_trans h₁ h₂)
        end,
        case or.inr : ex begin
          exact exists.elim ex begin
            assume p : convergence_space α,
            assume h' : p ∈ ps ∧ converges_ p l' x,
            exact or.inr (exists.intro p (and.intro h'.left (le_converges_ p h₁ h'.right)))
          end,
        end,
    end,
  }
}

-------------------------------------------------------------------------------
-- Lattice of convergence spaces
-------------------------------------------------------------------------------

instance : semilattice_sup (convergence_space α) := {
  le_sup_left := begin
    assume p q : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ p l x,
    exact or.inl h,
  end,
  le_sup_right := begin
    assume p q : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ q l x,
    exact or.inr h,
  end,
  sup_le := begin
    assume p q r : convergence_space α,
    assume h₁ : p ≤ r,
    assume h₂ : q ≤ r,
    assume l : filter α,
    assume x : α,
    assume h : converges_ (p ⊔ q) l x,
    cases h,
      exact h₁ h,
      exact h₂ h,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_sup,
}

instance : complete_semilattice_Sup (convergence_space α) := {
  le_Sup := begin
    assume ps : set (convergence_space α),
    assume p : convergence_space α,
    assume h : p ∈ ps,
    assume l : filter α,
    assume x : α,
    assume h' : converges_ p l x,
    exact or.inr (exists.intro p (and.intro h h')),
  end,
  Sup_le := begin
    assume qs : set (convergence_space α),
    assume p : convergence_space α,
    assume f : ∀ q ∈ qs, q ≤ p,
    assume l : filter α,
    assume x : α,
    assume h : converges_ (Sup qs) l x,
    cases h,
      case or.inl : le₁ begin
        exact le_converges_ p le₁ (pure_converges_ p x)
      end,
      case or.inr : ex begin
        exact exists.elim ex begin
          assume q : convergence_space α,
          assume h' : q ∈ qs ∧ converges_ q l x,
          exact (f q h'.left) h'.right
        end,
      end,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_Sup,
}

instance : semilattice_inf (convergence_space α) := {
  inf_le_left := begin
    assume p q : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ (p ⊓ q) l x,
    exact h.left,
  end,
  inf_le_right := begin
    assume p q : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ (p ⊓ q) l x,
    exact h.right,
  end,
  le_inf := begin
    assume p q r : convergence_space α,
    assume h₁ : p ≤ q,
    assume h₂ : p ≤ r,
    assume l : filter α,
    assume x : α,
    assume hp : converges_ p l x,
    have hq : converges_ q l x, from h₁ hp,
    have hr : converges_ r l x, from h₂ hp,
    exact and.intro hq hr
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_inf,
}

instance : complete_semilattice_Inf (convergence_space α) := {
  Inf_le := begin
    assume ps : set (convergence_space α),
    assume p : convergence_space α,
    assume h : p ∈ ps,
    assume l : filter α,
    assume x : α,
    assume h' : converges_ (Inf ps) l x,
    exact h' h,
  end,
  le_Inf := begin
    assume ps : set (convergence_space α),
    assume q : convergence_space α,
    assume f : ∀ p : convergence_space α, p ∈ ps → q ≤ p,
    assume l : filter α,
    assume x : α,
    assume h : converges_ q l x,
    assume p : convergence_space α,
    assume h' : p ∈ ps,
    exact (f p h') h,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_Inf,
}

instance : lattice (convergence_space α) := {
  ..convergence_space.semilattice_sup,
  ..convergence_space.semilattice_inf,
}

instance : complete_lattice (convergence_space α) := {
  bot_le := begin
    assume p : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ discrete l x,
    exact le_converges_ p h (pure_converges_ p x),
  end,
  le_top := begin
    assume p : convergence_space α,
    assume l : filter α,
    assume x : α,
    assume h : converges_ p l x,
    tauto,
  end,
  ..convergence_space.lattice,
  ..convergence_space.complete_semilattice_Sup,
  ..convergence_space.complete_semilattice_Inf,
  ..convergence_space.has_top,
  ..convergence_space.has_bot,
}

-------------------------------------------------------------------------------
-- Continuity
-------------------------------------------------------------------------------

def continuous [convergence_space α] [convergence_space β] (f : α → β) : Prop :=
∀ ⦃x l⦄, converges l x → converges (map f l) (f x)

lemma continuous.comp
[convergence_space α] [convergence_space β] [convergence_space γ] {g : β → γ} {f : α → β}
(hg : continuous g) (hf : continuous f) : continuous (g ∘ f) := begin
  assume x : α,
  assume l : filter α,
  assume : converges l x,
  have : converges (map f l) (f x), from hf this,
  have : converges (map g (map f l)) (g (f x)), from hg this,
  convert this,
end

lemma continuous_id [convergence_space α] : continuous (id : α → α) := begin
  assume x : α,
  assume l : filter α,
  assume : converges l x,
  simp [filter.map_id],
  exact this,
end

structure homeomorph (α β : Type*) [convergence_space α] [convergence_space β] extends α ≃ β :=
(continuous_to_fun : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

-------------------------------------------------------------------------------
-- Induced/coinduced convergence space
-------------------------------------------------------------------------------

/-- Given `f : α → β`, where `β` is convergence space, the induced convergence
 -- structure on `α` is the greatest convergence structure making `f`
 -- continuous. -/
def convergence_space.induced (f : α → β) [convergence_space β] : convergence_space α := {
  converges := λ l x, converges (map f l) (f x),
  pure_converges := by simp [filter.map_pure, pure_converges],
  le_converges := begin
    assume l l' : filter α,
    assume le₁ : l ≤ l',
    assume x : α,
    assume h : converges (map f l') (f x),
    have le₂ : map f l ≤ map f l', apply map_mono le₁,
    apply le_converges le₂ h
  end,
}

lemma continuous.induced_le (f : α → β) [p : convergence_space α] [convergence_space β] (hf : continuous f)
: p ≤ convergence_space.induced f
:= begin
  unfold has_le.le,
  assume l : filter α,
  assume x : α,
  assume h : converges_ p l x,
  exact hf h,
end

inductive coinduced_converges (f : α → β) [convergence_space α] (l' : filter β) (y : β) : Prop
| pure_case (_ : l' ≤ pure y) : coinduced_converges
| other_case (l : filter α) (x : α) (_ : l' ≤ map f l) (_ : y = f x) (_ : converges l x) : coinduced_converges

/-- Given `f : α → β`, where `α` is convergence space, the coinduced convergence
 -- structure on `β` is the least convergence structure making `f`
 -- continuous. -/
def convergence_space.coinduced (f : α → β) [convergence_space α] : convergence_space β := {
  converges := coinduced_converges f,
  pure_converges := λ y, coinduced_converges.pure_case (le_refl (pure y)),
  le_converges := begin
    assume l'₁ l'₂ : filter β,
    assume : l'₁ ≤ l'₂,
    assume y : β,
    assume h : coinduced_converges f l'₂ y,
    cases h,
      case pure_case begin
        have : l'₁ ≤ pure y, from calc
          l'₁ ≤ l'₂ : (by assumption : l'₁ ≤ l'₂)
          ... ≤ pure y : (by assumption : l'₂ ≤ pure y),
        exact coinduced_converges.pure_case (by assumption : l'₁ ≤ pure y),
      end,
      case other_case : l x _ _ _ begin
        have : l'₁ ≤ map f l, from calc
          l'₁ ≤ l'₂ : (by assumption : l'₁ ≤ l'₂)
          ... ≤ map f l : (by assumption : l'₂ ≤ map f l),
        exact coinduced_converges.other_case l x
          (by assumption : l'₁ ≤ map f l)
          (by assumption : y = f x)
          (by assumption : converges l x)
        end
  end,
}

lemma continuous.le_coinduced (f : α → β) [convergence_space α] [q : convergence_space β] (hf : continuous f)
: convergence_space.coinduced f ≤ q
:= begin
  unfold has_le.le,
  assume l' : filter β,
  assume y : β,
  assume h : converges_ (convergence_space.coinduced f) l' y,
  cases h,
    case pure_case begin
      exact le_converges_ q h (pure_converges_ q y),
    end,
    case other_case : l x h₀ h₁ h₂ begin
      have : converges_ q (map f l) (f x), from hf h₂,
      rw h₁,
      exact le_converges_ q h₀ this,
    end
end

-------------------------------------------------------------------------------
-- Limits, adherence, interior, closure, open, closed, neighborhoods
-------------------------------------------------------------------------------

section
variables [convergence_space α]
def lim (l : filter α) : set α := { x | converges l x }
def adheres (l : filter α) (x : α) : Prop := ∃ l' ≤ l, converges l' x
def adh (l : filter α) : set α := { x | adheres l x }
def interior (A : set α) : set α := { x ∈ A | ∀ l, converges l x → A ∈ l }
def is_open (A : set α) : Prop := A = interior A
def cl (A : set α) : set α := { x | ∃ (l : filter α) [ne_bot l], converges l x ∧ A ∈ l }
def is_closed (A : set α) : Prop := A = cl A
def is_dense (A : set α) : Prop := ∀ x, x ∈ cl A
def is_strictly_dense (A : set α) : Prop :=
∀ {x : α} {l : filter α}, converges l x → ∃ l', (A ∈ l') ∧ (converges l' x) ∧ (l ≤ filter.generate (cl '' l.sets))
def nhds (x : α) : filter α := ⨅ l ∈ {l' : filter α | converges l' x}, l
end

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

instance {p : α → Prop} [convergence_space α] : convergence_space (subtype p) :=
convergence_space.induced (coe : subtype p → α)

instance {r : α → α → Prop} [convergence_space α] : convergence_space (quot r) :=
convergence_space.coinduced (quot.mk r)

instance [convergence_space α] [convergence_space β] : convergence_space (α × β) :=
convergence_space.induced prod.fst ⊓ convergence_space.induced prod.snd

/-
lemma prod_fst_continuous [convergence_space α] [convergence_space β]
: continuous (prod.fst : α × β → α)
:= begin
  unfold continuous,
  assume p : α × β,
  assume l : filter (α × β),
  assume h : converges l p,
  have : converges_ (convergence_space.induced prod.fst) l p.fst, from
  --have : converges_ (convergence_space.induced prod.fst)
end
-/

instance [convergence_space α] : convergence_space (option α) :=
convergence_space.coinduced some

-------------------------------------------------------------------------------
-- The convergence space C(α,β)
-------------------------------------------------------------------------------

structure continuous_map (α β : Type*) [convergence_space α] [convergence_space β] :=
(to_fun : α → β)
(continuous_to_fun : continuous to_fun)

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

variables [convergence_space α] [convergence_space β]

instance : has_coe_to_fun (C(α, β)) (λ _, α → β) := ⟨continuous_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) := rfl

def eval (fx : C(α,β) × α) : β := fx.1 fx.2

variables {α β} {f g : continuous_map α β}

@[simp] theorem eval_comp_prod : eval ∘ prod.mk f = f := begin
  apply funext,
  assume x : α,
  apply comp_apply,
end

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

end continuous_map

instance [convergence_space α] [convergence_space β] : convergence_space C(α, β) := {
  converges := λ l f, ∀ (x : α) (l' : filter α), converges l' x → converges (map continuous_map.eval (l ×ᶠ l')) (f x),
  pure_converges := begin
    assume f : C(α, β),
    assume x : α,
    assume l' : filter α,
    assume h : converges l' x,
    have h' : map continuous_map.eval (pure f ×ᶠ l') = map f l', from calc
      map continuous_map.eval (pure f ×ᶠ l') = map continuous_map.eval (map (prod.mk f) l') : by simp [filter.pure_prod]
      ... = map (continuous_map.eval ∘ prod.mk f) l' : by simp [filter.map_map]
      ... = map f l' : by simp [continuous_map.eval_comp_prod],
    rw h',
    exact f.continuous_to_fun h
  end,
  le_converges := begin
    assume l l' : filter C(α, β),
    assume le₁ : l ≤ l',
    assume f : C(α, β),
    intro h, -- h : converges l' f,
    assume x : α,
    assume l'' : filter α,
    assume h' : converges l'' x,
    have le₂ : l ×ᶠ l'' ≤ l' ×ᶠ l'', from filter.prod_mono le₁ (partial_order.le_refl l''),
    have le₃ : map continuous_map.eval (l ×ᶠ l'') ≤ map continuous_map.eval (l' ×ᶠ l''), from filter.map_mono le₂,
    exact le_converges le₃ (h x l'' h'),
  end,
}

-------------------------------------------------------------------------------
-- Separation axioms
-------------------------------------------------------------------------------

class t0_space (α : Type*) [convergence_space α] : Prop :=
(t0_prop : ∀ x y : α, converges (pure x) y → converges (pure y) x → x = y)

class r0_space (α : Type*) [convergence_space α] : Prop :=
(r0_prop : ∀ x y, converges (pure x) y → ∀ (l : filter α), converges l x ↔ converges l y)

class t1_space (α : Type*) [convergence_space α] : Prop :=
(t1_prop : ∀ x y : α, converges (pure x) y → x = y)

class r1_space (α : Type*) [convergence_space α] : Prop :=
(r1_prop : ∀ x y, ∃ (l : filter α) [ne_bot l], converges l x ∧ converges l y → ∀ (l' : filter α), converges l' x ↔ converges l' y)

class t2_space (α : Type*) [convergence_space α] : Prop :=
(t2_prop : ∀ x y, ∀ (l : filter α) [ne_bot l], converges l x ∧ converges l y → x = y)

class r2_space (α : Type*) [convergence_space α] : Prop :=
(r2_prop : ∀ (x : α) (l : filter α), converges l x → converges (filter.generate (cl '' l.sets)) x)

class t3_space (α : Type*) [convergence_space α] extends t0_space α, r2_space α.

-------------------------------------------------------------------------------
-- Compact sets/spaces
-------------------------------------------------------------------------------

def is_compact [convergence_space α] (A : set α) := ∀ ⦃l : ultrafilter α⦄, A ∈ l → ∃ x, converges l.to_filter x

class compact_space (α : Type*) [convergence_space α] : Prop :=
(compact_prop : is_compact (univ : set α))

theorem is_compact.image {f : α → β} {A : set α} [convergence_space α] [convergence_space β]
  (h₀ : is_compact A) (h₁ : continuous f) : is_compact (f '' A) :=
begin
  unfold is_compact,
  assume 𝒱 : ultrafilter β,
  assume h₂ : f '' A ∈ 𝒱,
  let 𝒰 := ultrafilter.of_comap_inf_principal h₂,
  let h₃ : ultrafilter.map f 𝒰 = 𝒱 := ultrafilter.of_comap_inf_principal_eq_of_map h₂,
  let h₄ : A ∈ 𝒰 := ultrafilter.of_comap_inf_principal_mem h₂,
  obtain ⟨x, h₅ : converges 𝒰.to_filter x⟩ := h₀ h₄,
  have : converges (map f 𝒰) (f x) := h₁ h₅,
  rw ← h₃,
  use f x,
  tauto,
end

-------------------------------------------------------------------------------
-- Quotient maps
-------------------------------------------------------------------------------

def quotient_map [convergence_space α] [q : convergence_space β] (f : α → β) : Prop :=
surjective f ∧ q = convergence_space.coinduced f

lemma quotient_map_iff [convergence_space α] [q : convergence_space β] {f : α → β} :
quotient_map f ↔ surjective f ∧ ∀ l' y, converges l' y ↔ ∃ l x, (l' ≤ map f l) ∧ (y = f x) ∧ (converges l x) := begin
  split,
  -- Proving → direction.
  assume h : quotient_map f,
  split,
  exact h.1,
  assume l' : filter β,
  assume y : β,
  split,
  rw h.2,
  assume h' : converges_ (convergence_space.coinduced f) l' y,
  cases h',
    case pure_case begin
      obtain ⟨x, hx⟩ := h.1 y,
      rw ← hx at h',
      rw ← filter.map_pure at h',
      exact ⟨pure x, x, h', eq.symm hx, pure_converges x⟩,
    end,
    case other_case : l x h₁ h₂ h₃ begin
      exact ⟨l, x, h₁, h₂, h₃⟩,
    end,
  rintro ⟨l : filter α, x : α, h₁ : l' ≤ map f l, h₂ : y = f x, h₃ : converges l x⟩,
  rw h.2,
  exact coinduced_converges.other_case l x h₁ h₂ h₃,
  -- Proving ← direction
  intro h,
  unfold quotient_map,
  split,
  exact h.1,
  rw convergence_space_eq_iff,
  assume l' : filter β,
  assume y : β,
  rw h.2,
  split,
  rintro ⟨l : filter α, x : α, h₁ : l' ≤ map f l, h₂ : y = f x, h₃ : converges l x⟩,
  exact coinduced_converges.other_case l x h₁ h₂ h₃,
  assume h' : converges_ (convergence_space.coinduced f) l' y,
  cases h',
    case pure_case begin
      obtain ⟨x, hx⟩ := h.1 y,
      rw ← hx at h',
      rw ← filter.map_pure at h',
      exact ⟨pure x, x, h', eq.symm hx, pure_converges x⟩,
    end,
    case other_case : l x h₁ h₂ h₃ begin
      exact ⟨l, x, h₁, h₂, h₃⟩,
    end,
 end

/-
lemma quotient_prod_map
{α₁ β₁ : Type*} [p₁ : convergence_space α₁] [q₁ : convergence_space β₁] {f₁ : α₁ → β₁} (h₁ : quotient_map f₁)
{α₂ β₂ : Type*} [p₂ : convergence_space α₂] [q₂ : convergence_space β₂] {f₂ : α₂ → β₂} (h₂ : quotient_map f₂)
: quotient_map (prod.map f₁ f₂) := begin
  rw quotient_map_iff,
  rw quotient_map_iff at h₁,
  rw quotient_map_iff at h₂,
  split,
  exact surjective.prod_map h₁.1 h₂.1,
  rintros (l' : filter (β₁ × β₂)) (⟨y₁, y₂⟩ : β₁ × β₂),
  split,
  assume h : prod.convergence_space.converges l' (y₁, y₂),
  let l'₁ := map prod.fst l',
  let l'₂ := map prod.snd l',
  have hy₁ : q₁.converges l'₁ y₁, sorry,
  have hy₂ : q₂.converges l'₂ y₂, sorry,
  obtain ⟨l₁, x₁, le₁, eq₁, converges₁⟩ := (h₁.2 l'₁ y₁).mp hy₁,
  obtain ⟨l₂, x₂, le₂, eq₂, converges₂⟩ := (h₂.2 l'₂ y₂).mp hy₂,
  let l := l₁ ×ᶠ l₂,
  let x := (x₁, x₂),
  use l,
  use x,
end
-/

-------------------------------------------------------------------------------
-- Category Conv of convergence spaces
-------------------------------------------------------------------------------

universe u

def Conv : Type (u+1) := bundled convergence_space
