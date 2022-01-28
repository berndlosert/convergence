import tactic
import order.filter.partial
import order.filter.ultrafilter
import order.filter.bases
import algebra.support
import category_theory.concrete_category.bundled

noncomputable theory
open set function filter classical option category_theory
open_locale classical filter

variables {X Y Z : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

class convergence_space (X : Type*) :=
(converges : filter X → X → Prop)
(pure_converges : ∀ x, converges (pure x) x)
(le_converges : ∀ {ℱ 𝒢}, ℱ ≤ 𝒢 → ∀ {x}, converges 𝒢 x → converges ℱ x) -- ℱ ≤ 𝒢 means 𝒢 ⊆ ℱ

attribute [ext] convergence_space

open convergence_space

section
variables (p : convergence_space X)
def converges_ (ℱ : filter X) (x : X) : Prop := @converges _ p ℱ x
def pure_converges_ (x : X) : converges (pure x) x := @pure_converges _ p x
def le_converges_ {ℱ 𝒢 : filter X} (h : ℱ ≤ 𝒢) {x : X} (h' : converges 𝒢 x) : converges ℱ x
:= @le_converges _ p _ _ h _ h'
end

theorem convergence_space_eq_iff {p q : convergence_space X} :
p = q ↔ ∀ ℱ x, @converges _ p ℱ x ↔ @converges _ q ℱ x :=
by simp [funext_iff, convergence_space.ext_iff p q]

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space X) := {
  le := λ p q, ∀ {ℱ} {x}, @converges _ q ℱ x → @converges _ p ℱ x
}

instance : partial_order (convergence_space X) := {
  le_refl := begin
    assume p : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ p ℱ x,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space X,
    assume le₁ : p ≤ q,
    assume le₂ : q ≤ r,
    assume l : filter X,
    assume x : X,
    assume h : converges_ r l x,
    exact (le₁ (le₂ h))
  end,
  le_antisymm := begin
    assume p q : convergence_space X,
    assume le₁ : p ≤ q,
    assume le₂ : q ≤ p,
    ext l x,
    exact iff.intro le₂ le₁,
  end,
  ..convergence_space.has_le
}

-------------------------------------------------------------------------------
-- Discrete/indiscrete convergence spaces
-------------------------------------------------------------------------------

/-- In an indiscrete convergence space, every filter converges to every
 -- point. -/
def indiscrete : convergence_space X := {
  converges := λ ℱ x, true,
  pure_converges := by tauto,
  le_converges := by tauto,
}

/-- In a discrete convergence space, the only proper filters that converge are
 -- the `pure` ones. -/
def discrete : convergence_space X := {
  converges := λ ℱ x, ℱ ≤ pure x,
  pure_converges := by tauto,
  le_converges := by tauto,
}

instance : has_bot (convergence_space X) := {
  bot := indiscrete
}

instance : has_top (convergence_space X) := {
  top := discrete
}

-------------------------------------------------------------------------------
-- Supremum and infimum of convergence spaces
-------------------------------------------------------------------------------

instance : has_sup (convergence_space X) := {
  sup := λ p q, {
    converges := fun ℱ x, and (converges_ p ℱ x) (converges_ q ℱ x),
    pure_converges := begin
      assume x : X,
      exact and.intro (pure_converges_ p x) (pure_converges_ q x),
    end,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume h : ℱ ≤ 𝒢,
      assume x : X,
      assume h' : and (converges_ p 𝒢 x) (converges_ q 𝒢 x),
      exact and.intro (le_converges_ p h h'.left) (le_converges_ q h h'.right)
    end,
  }
}

instance : has_Sup (convergence_space X) := {
  Sup := λ ps, {
    converges := λ ℱ x, ∀ {p : convergence_space X}, p ∈ ps → converges_ p ℱ x,
    pure_converges := begin
      assume x : X,
      assume p : convergence_space X,
      assume : p ∈ ps,
      exact pure_converges_ p x,
    end,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume h : ℱ ≤ 𝒢,
      assume x : X,
      assume f : ∀ {p : convergence_space X}, p ∈ ps → converges_ p 𝒢 x,
      assume p : convergence_space X,
      assume h' : p ∈ ps,
      exact le_converges_ p h (f h')
    end,
  }
}

instance : has_inf (convergence_space X) := {
  inf := λ p q, {
    converges := λ ℱ x, or (converges_ p ℱ x) (converges_ q ℱ x),
    pure_converges := begin
      assume x : X,
      exact or.inl (pure_converges_ p x),
    end,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume h : ℱ ≤ 𝒢,
      assume x : X,
      assume h' : or (converges_ p 𝒢 x) (converges_ q 𝒢 x),
      exact or.elim h'
        (assume hl, or.inl (le_converges_ p h hl))
        (assume hr, or.inr (le_converges_ q h hr))
    end,
  }
}

instance : has_Inf (convergence_space X) := {
  Inf := λ ps, {
    converges := λ ℱ x, or
      (ℱ ≤ pure x)
      (∃ p : convergence_space X, p ∈ ps ∧ converges_ p ℱ x),
    pure_converges := by tauto,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume le₁ : ℱ ≤ 𝒢,
      assume x : X,
      assume h : or
        (𝒢 ≤ pure x)
        (∃ p : convergence_space X, p ∈ ps ∧ converges_ p 𝒢 x),
      cases h,
        case or.inl : le₂ begin
          exact or.inl (le_trans le₁ le₂)
        end,
        case or.inr : ex begin
          exact exists.elim ex begin
            assume p : convergence_space X,
            assume h' : p ∈ ps ∧ converges_ p 𝒢 x,
            exact or.inr (exists.intro p (and.intro h'.left (le_converges_ p le₁ h'.right)))
          end,
        end,
    end,
  }
}

-------------------------------------------------------------------------------
-- Lattice of convergence spaces
-------------------------------------------------------------------------------

instance : semilattice_sup (convergence_space X) := {
  le_sup_left := begin
    assume p q : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ (p ⊔ q) ℱ x,
    exact h.left,
  end,
  le_sup_right := begin
    assume p q : convergence_space X,
    assume l : filter X,
    assume x : X,
    assume h : converges_ (p ⊔ q) l x,
    exact h.right,
  end,
  sup_le := begin
    assume p q r : convergence_space X,
    assume le₁ : p ≤ r,
    assume le₂ : q ≤ r,
    assume ℱ : filter X,
    assume x : X,
    assume hr : converges_ r ℱ x,
    have hp : converges_ p ℱ x, from le₁ hr,
    have hq : converges_ q ℱ x, from le₂ hr,
    exact and.intro hp hq
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_sup,
}

instance : complete_semilattice_Sup (convergence_space X) := {
  le_Sup := begin
    assume ps : set (convergence_space X),
    assume p : convergence_space X,
    assume h : p ∈ ps,
    assume ℱ : filter X,
    assume x : X,
    assume h' : converges_ (Sup ps) ℱ x,
    exact h' h,
  end,
  Sup_le := begin
    assume ps : set (convergence_space X),
    assume q : convergence_space X,
    assume f : ∀ p : convergence_space X, p ∈ ps → p ≤ q,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ q ℱ x,
    assume p : convergence_space X,
    assume h' : p ∈ ps,
    exact (f p h') h,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_Sup,
}

instance : semilattice_inf (convergence_space X) := {
  inf_le_left := begin
    assume p q : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ p ℱ x,
    exact or.inl h,
  end,
  inf_le_right := begin
    assume p q : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ q ℱ x,
    exact or.inr h,
  end,
  le_inf := begin
    assume p q r : convergence_space X,
    assume le₁ : p ≤ q,
    assume le₂ : p ≤ r,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ (q ⊓ r) ℱ x,
    cases h,
      exact le₁ h,
      exact le₂ h,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_inf,
}

instance : complete_semilattice_Inf (convergence_space X) := {
  Inf_le := begin
    assume ps : set (convergence_space X),
    assume p : convergence_space X,
    assume h : p ∈ ps,
    assume ℱ : filter X,
    assume x : X,
    assume h' : converges_ p ℱ x,
    exact or.inr (exists.intro p (and.intro h h')),
  end,
  le_Inf := begin
    assume qs : set (convergence_space X),
    assume p : convergence_space X,
    assume f : ∀ q ∈ qs, p ≤ q,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ (Inf qs) ℱ x,
    cases h,
      case or.inl : le₁ begin
        exact le_converges_ p le₁ (pure_converges_ p x)
      end,
      case or.inr : ex begin
        exact exists.elim ex begin
          assume q : convergence_space X,
          assume h' : q ∈ qs ∧ converges_ q ℱ x,
          exact (f q h'.left) h'.right
        end,
      end,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_Inf,
}

instance : lattice (convergence_space X) := {
  ..convergence_space.semilattice_sup,
  ..convergence_space.semilattice_inf,
}

instance : complete_lattice (convergence_space X) := {
  le_top := begin
    assume p : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ discrete ℱ x,
    exact le_converges_ p h (pure_converges_ p x),
  end,
  bot_le := begin
    assume p : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : converges_ p ℱ x,
    tauto,
  end,
  ..convergence_space.lattice,
  ..convergence_space.complete_semilattice_Sup,
  ..convergence_space.complete_semilattice_Inf,
  ..convergence_space.has_top,
  ..convergence_space.has_bot,
}

-------------------------------------------------------------------------------
-- Induced/coinduced convergence space
-------------------------------------------------------------------------------

/-- Given `f : X → Y` and a convergence on `Y`, the induced convergence on `X`
 -- is the coarsest convergence that makes `f` continuous. -/
def convergence_space.induced (f : X → Y) [convergence_space Y] : convergence_space X := {
  converges := λ ℱ x, converges (map f ℱ) (f x),
  pure_converges := by simp [filter.map_pure, pure_converges],
  le_converges := begin
    assume ℱ 𝒢 : filter X,
    assume le₁ : ℱ ≤ 𝒢,
    assume x : X,
    assume h : converges (map f 𝒢) (f x),
    have le₂ : map f ℱ ≤ map f 𝒢, apply map_mono le₁,
    apply le_converges le₂ h
  end,
}

inductive coinduced_converges (f : X → Y) [convergence_space X] (𝒢 : filter Y) (y : Y) : Prop
| pure_case (_ : 𝒢 ≤ pure y) : coinduced_converges
| other_case (ℱ : filter X) (x : X) (_ : 𝒢 ≤ map f ℱ) (_ : y = f x) (_ : converges ℱ x) : coinduced_converges

def convergence_space.coinduced (f : X → Y) [convergence_space X] : convergence_space Y := {
  converges := coinduced_converges f,
  pure_converges := λ y, coinduced_converges.pure_case (le_refl (pure y)),
  le_converges := begin
    assume 𝒢₁ 𝒢₂ : filter Y,
    assume : 𝒢₁ ≤ 𝒢₂,
    assume y : Y,
    assume h : coinduced_converges f 𝒢₂ y,
    cases h,
      case pure_case begin
        have : 𝒢₁ ≤ pure y, from calc
          𝒢₁ ≤ 𝒢₂ : (by assumption : 𝒢₁ ≤ 𝒢₂)
          ... ≤ pure y : (by assumption : 𝒢₂ ≤ pure y),
        exact coinduced_converges.pure_case (by assumption : 𝒢₁ ≤ pure y),
      end,
      case other_case : ℱ x _ _ _ begin
        have : 𝒢₁ ≤ map f ℱ, from calc
          𝒢₁ ≤ 𝒢₂ : (by assumption : 𝒢₁ ≤ 𝒢₂)
          ... ≤ map f ℱ : (by assumption : 𝒢₂ ≤ map f ℱ),
        exact coinduced_converges.other_case ℱ x
          (by assumption : 𝒢₁ ≤ map f ℱ)
          (by assumption : y = f x)
          (by assumption : converges ℱ x)
        end
  end,
}

-------------------------------------------------------------------------------
-- Limits, adherence, interior, closure, open, closed, neighborhoods
-------------------------------------------------------------------------------

section
variables [convergence_space X]
def lim (ℱ : filter X) : set X := { x | converges ℱ x }
def adheres (ℱ : filter X) (x : X) : Prop := ∃ 𝒢 ≤ ℱ, converges 𝒢 x
def adh (ℱ : filter X) : set X := { x | adheres ℱ x }
def interior (A : set X) : set X := { x ∈ A | ∀ ℱ, converges ℱ x → A ∈ ℱ }
def is_open (A : set X) : Prop := A = interior A
def cl (A : set X) : set X := { x | ∃ (ℱ : filter X) [ne_bot ℱ], converges ℱ x ∧ A ∈ ℱ }
def is_closed (A : set X) : Prop := A = cl A
def is_dense (A : set X) : Prop := ∀ x, x ∈ cl A
def is_strictly_dense (A : set X) : Prop :=
∀ {x : X} {ℱ : filter X}, converges ℱ x → ∃ 𝒢, (A ∈ 𝒢) ∧ (converges 𝒢 x) ∧ (ℱ ≤ filter.generate (cl '' ℱ.sets))
def nhds (x : X) : filter X := ⨅ ℱ ∈ {𝒢 : filter X | converges 𝒢 x}, ℱ
end

-------------------------------------------------------------------------------
-- Continuity
-------------------------------------------------------------------------------

def continuous [convergence_space X] [convergence_space Y] (f : X → Y) : Prop :=
∀ ⦃x ℱ⦄, converges ℱ x → converges (map f ℱ) (f x)

lemma continuous.comp
[convergence_space X] [convergence_space Y] [convergence_space Z] {g : Y → Z} {f : X → Y}
(hg : continuous g) (hf : continuous f) : continuous (g ∘ f) := begin
  assume x : X,
  assume ℱ : filter X,
  assume : converges ℱ x,
  have : converges (map f ℱ) (f x), from hf this,
  have : converges (map g (map f ℱ)) (g (f x)), from hg this,
  convert this,
end

lemma continuous_id [convergence_space X] : continuous (id : X → X) := begin
  assume x : X,
  assume ℱ : filter X,
  assume : converges ℱ x,
  simp [filter.map_id],
  exact this,
end

structure homeomorph (X Y : Type*) [convergence_space X] [convergence_space Y] extends X ≃ Y :=
(continuous_to_fun : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

instance {p : X → Prop} [convergence_space X] : convergence_space (subtype p) :=
convergence_space.induced (coe : subtype p → X)

instance {r : X → X → Prop} [convergence_space X] : convergence_space (quot r) :=
convergence_space.coinduced (quot.mk r)

instance [convergence_space X] [convergence_space Y] : convergence_space (X × Y) :=
convergence_space.induced prod.fst ⊓ convergence_space.induced prod.snd

instance [convergence_space X] : convergence_space (option X) :=
convergence_space.coinduced some

-------------------------------------------------------------------------------
-- The convergence space C(X,Y)
-------------------------------------------------------------------------------

structure continuous_map (X Y : Type*) [convergence_space X] [convergence_space Y] :=
(to_fun : X → Y)
(continuous_to_fun : continuous to_fun)

notation `C(` X `, ` Y `)` := continuous_map X Y

namespace continuous_map

variables [convergence_space X] [convergence_space Y]

instance : has_coe_to_fun (C(X, Y)) (λ _, X → Y) := ⟨continuous_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : C(X, Y)} : f.to_fun = (f : X → Y) := rfl

def eval (fx : C(X,Y) × X) : Y := fx.1 fx.2

variables {X Y} {f g : continuous_map X Y}

@[simp] theorem eval_comp_prod : eval ∘ prod.mk f = f := begin
  apply funext,
  assume x : X,
  apply comp_apply,
end

protected lemma continuous (f : C(X, Y)) : continuous f := f.continuous_to_fun

end continuous_map

instance [convergence_space X] [convergence_space Y] : convergence_space C(X, Y) := {
  converges := λ ℱ f, ∀ (x : X) (𝒢 : filter X), converges 𝒢 x → converges (map continuous_map.eval (ℱ ×ᶠ 𝒢)) (f x),
  pure_converges := begin
    assume f : C(X, Y),
    assume x : X,
    assume 𝒢 : filter X,
    assume h : converges 𝒢 x,
    have h' : map continuous_map.eval (pure f ×ᶠ 𝒢) = map f 𝒢, from calc
      map continuous_map.eval (pure f ×ᶠ 𝒢) = map continuous_map.eval (map (prod.mk f) 𝒢) : by simp [filter.pure_prod]
      ... = map (continuous_map.eval ∘ prod.mk f) 𝒢 : by simp [filter.map_map]
      ... = map f 𝒢 : by simp [continuous_map.eval_comp_prod],
    rw h',
    exact f.continuous_to_fun h
  end,
  le_converges := begin
    assume ℱ 𝒢 : filter C(X, Y),
    assume le₁ : ℱ ≤ 𝒢,
    assume f : C(X, Y),
    intro h, -- h : converges 𝒢 f,
    assume x : X,
    assume 𝒢' : filter X,
    assume h' : converges 𝒢' x,
    have le₂ : ℱ ×ᶠ 𝒢' ≤ 𝒢 ×ᶠ 𝒢', from filter.prod_mono le₁ (partial_order.le_refl 𝒢'),
    have le₃ : map continuous_map.eval (ℱ ×ᶠ 𝒢') ≤ map continuous_map.eval (𝒢 ×ᶠ 𝒢'), from filter.map_mono le₂,
    exact le_converges le₃ (h x 𝒢' h'),
  end,
}

-------------------------------------------------------------------------------
-- Separation axioms
-------------------------------------------------------------------------------

class t0_space (X : Type*) [convergence_space X] : Prop :=
(t0_prop : ∀ x y : X, converges (pure x) y → converges (pure y) x → x = y)

class r0_space (X : Type*) [convergence_space X] : Prop :=
(r0_prop : ∀ x y, converges (pure x) y → ∀ (ℱ : filter X), converges ℱ x ↔ converges ℱ y)

class t1_space (X : Type*) [convergence_space X] : Prop :=
(t1_prop : ∀ x y : X, converges (pure x) y → x = y)

class r1_space (X : Type*) [convergence_space X] : Prop :=
(r1_prop : ∀ x y, ∃ (ℱ : filter X) [ne_bot ℱ], converges ℱ x ∧ converges ℱ y → ∀ (𝒢 : filter X), converges 𝒢 x ↔ converges 𝒢 y)

class t2_space (X : Type*) [convergence_space X] : Prop :=
(t2_prop : ∀ x y, ∀ (ℱ : filter X) [ne_bot ℱ], converges ℱ x ∧ converges ℱ y → x = y)

class r2_space (X : Type*) [convergence_space X] : Prop :=
(r2_prop : ∀ (x : X) (ℱ : filter X), converges ℱ x → converges (filter.generate (cl '' ℱ.sets)) x)

class t3_space (X : Type*) [convergence_space X] extends t0_space X, r2_space X.

-------------------------------------------------------------------------------
-- Compact sets/spaces
-------------------------------------------------------------------------------

def is_compact [convergence_space X] (A : set X) := ∀ ⦃ℱ : ultrafilter X⦄, A ∈ ℱ → ∃ x, converges ℱ.to_filter x

class compact_space (X : Type*) [convergence_space X] : Prop :=
(compact_prop : is_compact (univ : set X))

theorem is_compact.image {f : X → Y} {A : set X} [convergence_space X] [convergence_space Y]
  (h₀ : is_compact A) (h₁ : continuous f) : is_compact (f '' A) :=
begin
  unfold is_compact,
  assume 𝒱 : ultrafilter Y,
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

---------------------------------------------------------------------------------
---- Quotient maps
---------------------------------------------------------------------------------
--
--def quotient_map [p : convergence_space X] [q : convergence_space Y] (f : X → Y) : Prop :=
--surjective f ∧ q = convergence_space.coinduced f p
--
--lemma quotient_map_iff [p : convergence_space X] [q : convergence_space Y] {f : X → Y} :
--quotient_map f ↔ surjective f ∧ ∀ 𝒢 y, q.converges 𝒢 y ↔ ∃ ℱ x, (𝒢 ≤ map f ℱ) ∧ (y = f x) ∧ (p.converges ℱ x) := begin
--  split,
--  -- Proving → direction.
--  assume h : quotient_map f,
--  split,
--  exact h.1,
--  assume 𝒢 : filter Y,
--  assume y : Y,
--  split,
--  rw h.2,
--  assume h' : (convergence_space.coinduced f p).converges 𝒢 y,
--  cases h',
--    case pure_case begin
--      obtain ⟨x, hx⟩ := h.1 y,
--      rw ← hx at h',
--      rw ← filter.map_pure at h',
--      exact ⟨pure x, x, h', eq.symm hx, p.pure_converges x⟩,
--    end,
--    case other_case : ℱ x h₁ h₂ h₃ begin
--      exact ⟨ℱ, x, h₁, h₂, h₃⟩,
--    end,
--  rintro ⟨ℱ : filter X, x : X, h₁ : 𝒢 ≤ map f ℱ, h₂ : y = f x, h₃ : p.converges ℱ x⟩,
--  rw h.2,
--  exact coinduced_converges.other_case ℱ x h₁ h₂ h₃,
--  -- Proving ← direction
--  intro h,
--  unfold quotient_map,
--  split,
--  exact h.1,
--  rw convergence_space_eq_iff,
--  assume 𝒢 : filter Y,
--  assume y : Y,
--  rw h.2,
--  split,
--  rintro ⟨ℱ : filter X, x : X, h₁ : 𝒢 ≤ map f ℱ, h₂ : y = f x, h₃ : p.converges ℱ x⟩,
--  exact coinduced_converges.other_case ℱ x h₁ h₂ h₃,
--  assume h' : (convergence_space.coinduced f p).converges 𝒢 y,
--  cases h',
--    case pure_case begin
--      obtain ⟨x, hx⟩ := h.1 y,
--      rw ← hx at h',
--      rw ← filter.map_pure at h',
--      exact ⟨pure x, x, h', eq.symm hx, p.pure_converges x⟩,
--    end,
--    case other_case : ℱ x h₁ h₂ h₃ begin
--      exact ⟨ℱ, x, h₁, h₂, h₃⟩,
--    end,
-- end
--
--/-
--lemma quotient_prod_map
--{X₁ Y₁ : Type*} [p₁ : convergence_space X₁] [q₁ : convergence_space Y₁] {f₁ : X₁ → Y₁} (h₁ : quotient_map f₁)
--{X₂ Y₂ : Type*} [p₂ : convergence_space X₂] [q₂ : convergence_space Y₂] {f₂ : X₂ → Y₂} (h₂ : quotient_map f₂)
--: quotient_map (prod.map f₁ f₂) := begin
--  rw quotient_map_iff,
--  rw quotient_map_iff at h₁,
--  rw quotient_map_iff at h₂,
--  split,
--  exact surjective.prod_map h₁.1 h₂.1,
--  rintros (𝒢 : filter (Y₁ × Y₂)) (⟨y₁, y₂⟩ : Y₁ × Y₂),
--  split,
--  assume h : prod.convergence_space.converges 𝒢 (y₁, y₂),
--  let 𝒢₁ := map prod.fst 𝒢,
--  let 𝒢₂ := map prod.snd 𝒢,
--  have hy₁ : q₁.converges 𝒢₁ y₁, sorry,
--  have hy₂ : q₂.converges 𝒢₂ y₂, sorry,
--  obtain ⟨ℱ₁, x₁, le₁, eq₁, converges₁⟩ := (h₁.2 𝒢₁ y₁).mp hy₁,
--  obtain ⟨ℱ₂, x₂, le₂, eq₂, converges₂⟩ := (h₂.2 𝒢₂ y₂).mp hy₂,
--  let ℱ := ℱ₁ ×ᶠ ℱ₂,
--  let x := (x₁, x₂),
--  use ℱ,
--  use x,
--end
---/
--
---------------------------------------------------------------------------------
---- Category Conv of convergence spaces
---------------------------------------------------------------------------------
--
--universe u
--
--def Conv : Type (u+1) := bundled convergence_space
