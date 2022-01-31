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
(pure_converges : ∀ a, converges (pure a) a)
(le_converges : ∀ {l l'}, l ≤ l' → ∀ {a}, converges l' a → converges l a)

open convergence_space

section
variables (p : convergence_space α)
def converges_ (l : filter α) (a : α) : Prop := @converges _ p l a
def pure_converges_ (a : α) : converges (pure a) a := @pure_converges _ p a
def le_converges_ ⦃l l' : filter α⦄ (h : l ≤ l') {a : α} (h' : converges l' a) : converges l a
:= @le_converges _ p _ _ h _ h'
end

theorem convergence_space_eq_iff {p q : convergence_space α} :
p = q ↔ ∀ l a, @converges _ p l a ↔ @converges _ q l a :=
by simp [funext_iff, convergence_space.ext_iff p q]

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space α) := {
  le := λ p q, ∀ {l} {a}, @converges _ p l a → @converges _ q l a
}

instance : partial_order (convergence_space α) := {
  le_refl := begin
    assume p : convergence_space α,
    assume l : filter α,
    assume a : α,
    assume h : converges_ p l a,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space α,
    assume h₁ : p ≤ q,
    assume h₂ : q ≤ r,
    assume l : filter α,
    assume a : α,
    assume h : converges_ p l a,
    exact (h₂ (h₁ h))
  end,
  le_antisymm := begin
    assume p q : convergence_space α,
    assume h₁ : p ≤ q,
    assume h₂ : q ≤ p,
    ext l a,
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
  converges := λ l a, true,
  pure_converges := by tauto,
  le_converges := by tauto,
}

instance : has_top (convergence_space α) := {
  top := indiscrete
}

/-- The discrete convergence structure is the one where the only proper filters
 -- that converge are the `pure` ones. -/
def discrete : convergence_space α := {
  converges := λ l a, l ≤ pure a,
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
    converges := fun l a, and (converges_ p l a) (converges_ q l a),
    pure_converges := begin
      assume a : α,
      exact and.intro (pure_converges_ p a) (pure_converges_ q a),
    end,
    le_converges := begin
      assume l l' : filter α,
      assume h : l ≤ l',
      assume a : α,
      assume h' : and (converges_ p l' a) (converges_ q l' a),
      exact and.intro (le_converges_ p h h'.left) (le_converges_ q h h'.right)
    end,
  }
}

instance : has_Inf (convergence_space α) := {
  Inf := λ ps, {
    converges := λ l a, ∀ {p : convergence_space α}, p ∈ ps → converges_ p l a,
    pure_converges := begin
      assume a : α,
      assume p : convergence_space α,
      assume : p ∈ ps,
      exact pure_converges_ p a,
    end,
    le_converges := begin
      assume l l' : filter α,
      assume h : l ≤ l',
      assume a : α,
      assume f : ∀ {p : convergence_space α}, p ∈ ps → converges_ p l' a,
      assume p : convergence_space α,
      assume h' : p ∈ ps,
      exact le_converges_ p h (f h')
    end,
  }
}

instance : has_sup (convergence_space α) := {
  sup := λ p q, {
    converges := λ l a, or (converges_ p l a) (converges_ q l a),
    pure_converges := begin
      assume a : α,
      exact or.inl (pure_converges_ p a),
    end,
    le_converges := begin
      assume l l' : filter α,
      assume h : l ≤ l',
      assume a : α,
      assume h' : or (converges_ p l' a) (converges_ q l' a),
      exact or.elim h'
        (assume hl, or.inl (le_converges_ p h hl))
        (assume hr, or.inr (le_converges_ q h hr))
    end,
  }
}

instance : has_Sup (convergence_space α) := {
  Sup := λ ps, {
    converges := λ l a, or
      (l ≤ pure a)
      (∃ p : convergence_space α, p ∈ ps ∧ converges_ p l a),
    pure_converges := by tauto,
    le_converges := begin
      assume l l' : filter α,
      assume h₁ : l ≤ l',
      assume a : α,
      assume h : or
        (l' ≤ pure a)
        (∃ p : convergence_space α, p ∈ ps ∧ converges_ p l' a),
      cases h,
        case or.inl : h₂ begin
          exact or.inl (le_trans h₁ h₂)
        end,
        case or.inr : ea begin
          exact exists.elim ea begin
            assume p : convergence_space α,
            assume h' : p ∈ ps ∧ converges_ p l' a,
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
    assume a : α,
    assume h : converges_ p l a,
    exact or.inl h,
  end,
  le_sup_right := begin
    assume p q : convergence_space α,
    assume l : filter α,
    assume a : α,
    assume h : converges_ q l a,
    exact or.inr h,
  end,
  sup_le := begin
    assume p q r : convergence_space α,
    assume h₁ : p ≤ r,
    assume h₂ : q ≤ r,
    assume l : filter α,
    assume a : α,
    assume h : converges_ (p ⊔ q) l a,
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
    assume a : α,
    assume h' : converges_ p l a,
    exact or.inr (exists.intro p (and.intro h h')),
  end,
  Sup_le := begin
    assume qs : set (convergence_space α),
    assume p : convergence_space α,
    assume f : ∀ q ∈ qs, q ≤ p,
    assume l : filter α,
    assume a : α,
    assume h : converges_ (Sup qs) l a,
    cases h,
      case or.inl : le₁ begin
        exact le_converges_ p le₁ (pure_converges_ p a)
      end,
      case or.inr : ea begin
        exact exists.elim ea begin
          assume q : convergence_space α,
          assume h' : q ∈ qs ∧ converges_ q l a,
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
    assume a : α,
    assume h : converges_ (p ⊓ q) l a,
    exact h.left,
  end,
  inf_le_right := begin
    assume p q : convergence_space α,
    assume l : filter α,
    assume a : α,
    assume h : converges_ (p ⊓ q) l a,
    exact h.right,
  end,
  le_inf := begin
    assume p q r : convergence_space α,
    assume h₁ : p ≤ q,
    assume h₂ : p ≤ r,
    assume l : filter α,
    assume a : α,
    assume hp : converges_ p l a,
    have hq : converges_ q l a, from h₁ hp,
    have hr : converges_ r l a, from h₂ hp,
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
    assume a : α,
    assume h' : converges_ (Inf ps) l a,
    exact h' h,
  end,
  le_Inf := begin
    assume ps : set (convergence_space α),
    assume q : convergence_space α,
    assume h : ∀ p : convergence_space α, p ∈ ps → q ≤ p,
    assume l : filter α,
    assume a : α,
    assume hq : converges_ q l a,
    assume p : convergence_space α,
    assume hp : p ∈ ps,
    exact (h p hp) hq,
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
    assume a : α,
    assume h : converges_ discrete l a,
    exact le_converges_ p h (pure_converges_ p a),
  end,
  le_top := begin
    assume p : convergence_space α,
    assume l : filter α,
    assume a : α,
    assume h : converges_ p l a,
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
∀ ⦃a l⦄, converges l a → converges (map f l) (f a)

lemma continuous.comp
[convergence_space α] [convergence_space β] [convergence_space γ] {g : β → γ} {f : α → β}
(hg : continuous g) (hf : continuous f) : continuous (g ∘ f) := begin
  assume a : α,
  assume l : filter α,
  assume : converges l a,
  have : converges (map f l) (f a), from hf this,
  have : converges (map g (map f l)) (g (f a)), from hg this,
  convert this,
end

lemma continuous_id [convergence_space α] : continuous (id : α → α) := begin
  assume a : α,
  assume l : filter α,
  assume : converges l a,
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
 -- structure on `α` is the grextest convergence structure making `f`
 -- continuous. -/
def convergence_space.induced (f : α → β) [convergence_space β] : convergence_space α := {
  converges := λ l a, converges (map f l) (f a),
  pure_converges := by simp [filter.map_pure, pure_converges],
  le_converges := begin
    assume l l' : filter α,
    assume hl : l ≤ l',
    assume a : α,
    assume h : converges (map f l') (f a),
    have hl' : map f l ≤ map f l', apply map_mono hl,
    apply le_converges hl' h
  end,
}

lemma continuous.induced_le (f : α → β) [p : convergence_space α] [convergence_space β] (hf : continuous f)
: p ≤ convergence_space.induced f
:= begin
  unfold has_le.le,
  assume l : filter α,
  assume a : α,
  assume h : converges_ p l a,
  exact hf h,
end

inductive coinduced_converges (f : α → β) [convergence_space α] (lb : filter β) (y : β) : Prop
| pure_case (_ : lb ≤ pure y) : coinduced_converges
| other_case (la : filter α) (a : α) (_ : lb ≤ map f la) (_ : y = f a) (_ : converges la a) : coinduced_converges

/-- Given `f : α → β`, where `α` is convergence space, the coinduced convergence
 -- structure on `β` is the least convergence structure making `f`
 -- continuous. -/
def convergence_space.coinduced (f : α → β) [convergence_space α] : convergence_space β := {
  converges := coinduced_converges f,
  pure_converges := λ y, coinduced_converges.pure_case (le_refl (pure y)),
  le_converges := begin
    assume lb₁ lb₂ : filter β,
    assume : lb₁ ≤ lb₂,
    assume y : β,
    assume h : coinduced_converges f lb₂ y,
    cases h,
      case pure_case begin
        have : lb₁ ≤ pure y, from calc
          lb₁ ≤ lb₂ : (by assumption : lb₁ ≤ lb₂)
          ... ≤ pure y : (by assumption : lb₂ ≤ pure y),
        exact coinduced_converges.pure_case (by assumption : lb₁ ≤ pure y),
      end,
      case other_case : la a _ _ _ begin
        have : lb₁ ≤ map f la, from calc
          lb₁ ≤ lb₂ : (by assumption : lb₁ ≤ lb₂)
          ... ≤ map f la : (by assumption : lb₂ ≤ map f la),
        exact coinduced_converges.other_case la a
          (by assumption : lb₁ ≤ map f la)
          (by assumption : y = f a)
          (by assumption : converges la a)
        end
  end,
}

lemma continuous.le_coinduced (f : α → β) [convergence_space α] [q : convergence_space β] (hf : continuous f)
: convergence_space.coinduced f ≤ q
:= begin
  unfold has_le.le,
  assume lb : filter β,
  assume y : β,
  assume h : converges_ (convergence_space.coinduced f) lb y,
  cases h,
    case pure_case begin
      exact le_converges_ q h (pure_converges_ q y),
    end,
    case other_case : la a h₀ h₁ h₂ begin
      have : converges_ q (map f la) (f a), from hf h₂,
      rw h₁,
      exact le_converges_ q h₀ this,
    end
end

-------------------------------------------------------------------------------
-- Limits, adherence, interior, closure, open, closed, neighborhoods
-------------------------------------------------------------------------------

section
variables [convergence_space α]
def lim (l : filter α) : set α := { a | converges l a }
def adheres (l : filter α) (a : α) : Prop := ∃ l' ≤ l, converges l' a
def adh (l : filter α) : set α := { a | adheres l a }
def interior (s : set α) : set α := { a ∈ s | ∀ l, converges l a → s ∈ l }
def is_open (s : set α) : Prop := s = interior s
def cl (s : set α) : set α := { a | ∃ (l : filter α) [ne_bot l], converges l a ∧ s ∈ l }
def is_closed (s : set α) : Prop := s = cl s
def is_dense (s : set α) : Prop := ∀ a, a ∈ cl s
def is_strictly_dense (s : set α) : Prop :=
∀ {a : α} {l : filter α}, converges l a → ∃ l', (s ∈ l') ∧ (converges l' a) ∧ (l ≤ filter.generate (cl '' l.sets))
def nhds (a : α) : filter α := ⨅ l ∈ {l' : filter α | converges l' a}, l
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

def eval (fa : C(α,β) × α) : β := fa.1 fa.2

variables {α β} {f g : continuous_map α β}

@[simp] theorem eval_comp_prod : eval ∘ prod.mk f = f := begin
  apply funext,
  assume a : α,
  apply comp_apply,
end

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

end continuous_map

instance [convergence_space α] [convergence_space β] : convergence_space C(α, β) := {
  converges := λ l f, ∀ (a : α) (l' : filter α), converges l' a → converges (map continuous_map.eval (l ×ᶠ l')) (f a),
  pure_converges := begin
    assume f : C(α, β),
    assume a : α,
    assume l' : filter α,
    assume h : converges l' a,
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
    assume a : α,
    assume l'' : filter α,
    assume h' : converges l'' a,
    have le₂ : l ×ᶠ l'' ≤ l' ×ᶠ l'', from filter.prod_mono le₁ (partial_order.le_refl l''),
    have le₃ : map continuous_map.eval (l ×ᶠ l'') ≤ map continuous_map.eval (l' ×ᶠ l''), from filter.map_mono le₂,
    exact le_converges le₃ (h a l'' h'),
  end,
}

-------------------------------------------------------------------------------
-- Separation aaioms
-------------------------------------------------------------------------------

class t0_space (α : Type*) [convergence_space α] : Prop :=
(t0_prop : ∀ a y : α, converges (pure a) y → converges (pure y) a → a = y)

class r0_space (α : Type*) [convergence_space α] : Prop :=
(r0_prop : ∀ a y, converges (pure a) y → ∀ (l : filter α), converges l a ↔ converges l y)

class t1_space (α : Type*) [convergence_space α] : Prop :=
(t1_prop : ∀ a y : α, converges (pure a) y → a = y)

class r1_space (α : Type*) [convergence_space α] : Prop :=
(r1_prop : ∀ a y, ∃ (l : filter α) [ne_bot l], converges l a ∧ converges l y → ∀ (l' : filter α), converges l' a ↔ converges l' y)

class t2_space (α : Type*) [convergence_space α] : Prop :=
(t2_prop : ∀ a y, ∀ (l : filter α) [ne_bot l], converges l a ∧ converges l y → a = y)

class r2_space (α : Type*) [convergence_space α] : Prop :=
(r2_prop : ∀ (a : α) (l : filter α), converges l a → converges (filter.generate (cl '' l.sets)) a)

class t3_space (α : Type*) [convergence_space α] extends t0_space α, r2_space α.

-------------------------------------------------------------------------------
-- Compact sets/spaces
-------------------------------------------------------------------------------

def is_compact [convergence_space α] (s : set α) := ∀ ⦃l : ultrafilter α⦄, s ∈ l → ∃ a, converges l.to_filter a

class compact_space (α : Type*) [convergence_space α] : Prop :=
(compact_prop : is_compact (univ : set α))

theorem is_compact.image {f : α → β} {s : set α} [convergence_space α] [convergence_space β]
  (h₀ : is_compact s) (h₁ : continuous f) : is_compact (f '' s) :=
begin
  unfold is_compact,
  assume lb : ultrafilter β,
  assume h₂ : f '' s ∈ lb,
  let la := ultrafilter.of_comap_inf_principal h₂,
  let h₃ : ultrafilter.map f la = lb := ultrafilter.of_comap_inf_principal_eq_of_map h₂,
  let h₄ : s ∈ la := ultrafilter.of_comap_inf_principal_mem h₂,
  obtain ⟨a, h₅ : converges la.to_filter a⟩ := h₀ h₄,
  have : converges (map f la) (f a) := h₁ h₅,
  rw ← h₃,
  use f a,
  tauto,
end

-------------------------------------------------------------------------------
-- Quotient maps
-------------------------------------------------------------------------------

def quotient_map [convergence_space α] [q : convergence_space β] (f : α → β) : Prop :=
surjective f ∧ q = convergence_space.coinduced f

lemma quotient_map_iff [convergence_space α] [q : convergence_space β] {f : α → β} :
quotient_map f ↔ surjective f ∧ ∀ lb y, converges lb y ↔ ∃ la a, (lb ≤ map f la) ∧ (y = f a) ∧ (converges la a) := begin
  split,
  -- Proving → direction.
  assume h : quotient_map f,
  split,
  exact h.1,
  assume lb : filter β,
  assume y : β,
  split,
  rw h.2,
  assume h' : converges_ (convergence_space.coinduced f) lb y,
  cases h',
    case pure_case begin
      obtain ⟨a, ha⟩ := h.1 y,
      rw ← ha at h',
      rw ← filter.map_pure at h',
      exact ⟨pure a, a, h', eq.symm ha, pure_converges a⟩,
    end,
    case other_case : la a h₁ h₂ h₃ begin
      exact ⟨la, a, h₁, h₂, h₃⟩,
    end,
  rintro ⟨la : filter α, a : α, h₁ : lb ≤ map f la, h₂ : y = f a, h₃ : converges la a⟩,
  rw h.2,
  exact coinduced_converges.other_case la a h₁ h₂ h₃,
  -- Proving ← direction
  intro h,
  unfold quotient_map,
  split,
  exact h.1,
  rw convergence_space_eq_iff,
  assume lb : filter β,
  assume y : β,
  rw h.2,
  split,
  rintro ⟨la : filter α, a : α, h₁ : lb ≤ map f la, h₂ : y = f a, h₃ : converges la a⟩,
  exact coinduced_converges.other_case la a h₁ h₂ h₃,
  assume h' : converges_ (convergence_space.coinduced f) lb y,
  cases h',
    case pure_case begin
      obtain ⟨a, ha⟩ := h.1 y,
      rw ← ha at h',
      rw ← filter.map_pure at h',
      exact ⟨pure a, a, h', eq.symm ha, pure_converges a⟩,
    end,
    case other_case : la a h₁ h₂ h₃ begin
      exact ⟨la, a, h₁, h₂, h₃⟩,
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
  obtain ⟨l₁, a₁, le₁, eq₁, converges₁⟩ := (h₁.2 l'₁ y₁).mp hy₁,
  obtain ⟨l₂, a₂, le₂, eq₂, converges₂⟩ := (h₂.2 l'₂ y₂).mp hy₂,
  let l := l₁ ×ᶠ l₂,
  let a := (a₁, a₂),
  use l,
  use a,
end
-/

-------------------------------------------------------------------------------
-- Category Conv of convergence spaces
-------------------------------------------------------------------------------

universe u

def Conv : Type (u+1) := bundled convergence_space
