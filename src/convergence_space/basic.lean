import tactic
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup has_inf has_mem has_top has_bot

variables {X Y : Type*}
variables {a b : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

structure convergence_space (X : Type*) :=
(converges : filter X → X → Prop)
(pure_converges : ∀ x, converges (pure x) x)
(le_converges : ∀ {ℱ 𝒢}, ℱ ≤ 𝒢 → ∀ {x}, converges 𝒢 x → converges ℱ x) -- ℱ ≤ 𝒢 means 𝒢 ⊆ ℱ

attribute [ext] convergence_space
attribute [class] convergence_space

open convergence_space

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space X) := {
  le := λ p q, ∀ {ℱ} {x}, q.converges ℱ x → p.converges ℱ x
}

instance : partial_order (convergence_space X) := {
  le_refl := begin
    assume p : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : p.converges ℱ x,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space X,
    assume le₁ : p ≤ q,
    assume le₂ : q ≤ r,
    assume l : filter X,
    assume x : X,
    assume h : r.converges l x,
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

def indiscrete : convergence_space X := {
  converges := λ ℱ x, true,
  pure_converges := by tauto,
  le_converges := by tauto,
}

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
    converges := fun ℱ x, and (p.converges ℱ x) (q.converges ℱ x),
    pure_converges := begin
      assume x : X,
      exact and.intro (p.pure_converges x) (q.pure_converges x),
    end,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume h : ℱ ≤ 𝒢,
      assume x : X,
      assume h' : and (p.converges 𝒢 x) (q.converges 𝒢 x),
      exact and.intro (p.le_converges h h'.left) (q.le_converges h h'.right)
    end,
  }
}

instance : has_Sup (convergence_space X) := {
  Sup := λ ps, {
    converges := λ ℱ x, ∀ {p : convergence_space X}, p ∈ ps → p.converges ℱ x,
    pure_converges := begin
      assume x : X,
      assume p : convergence_space X,
      assume : p ∈ ps,
      exact p.pure_converges x,
    end,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume h : ℱ ≤ 𝒢,
      assume x : X,
      assume f : ∀ {p : convergence_space X}, p ∈ ps → p.converges 𝒢 x,
      assume p : convergence_space X,
      assume h' : p ∈ ps,
      exact p.le_converges h (f h')
    end,
  }
}

instance : has_inf (convergence_space X) := {
  inf := λ p q, {
    converges := λ ℱ x, or (p.converges ℱ x) (q.converges ℱ x),
    pure_converges := begin
      assume x : X,
      exact or.inl (p.pure_converges x),
    end,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume h : ℱ ≤ 𝒢,
      assume x : X,
      assume h' : or (p.converges 𝒢 x) (q.converges 𝒢 x),
      exact or.elim h'
        (assume hl, or.inl (p.le_converges h hl))
        (assume hr, or.inr (q.le_converges h hr))
    end,
  }
}

instance : has_Inf (convergence_space X) := {
  Inf := λ ps, {
    converges := λ ℱ x, or
      (ℱ ≤ pure x)
      (∃ p : convergence_space X, p ∈ ps ∧ p.converges ℱ x),
    pure_converges := by tauto,
    le_converges := begin
      assume ℱ 𝒢 : filter X,
      assume le₁ : ℱ ≤ 𝒢,
      assume x : X,
      assume h : or
        (𝒢 <= pure x)
        (∃ p : convergence_space X, p ∈ ps ∧ p.converges 𝒢 x),
      cases h,
        case or.inl : le₂ begin
          exact or.inl (le_trans le₁ le₂)
        end,
        case or.inr : ex begin
          exact exists.elim ex begin
            assume p : convergence_space X,
            assume h' : p ∈ ps ∧ p.converges 𝒢 x,
            exact or.inr (exists.intro p (and.intro h'.left (p.le_converges le₁ h'.right)))
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
    assume h : (sup p q).converges ℱ x,
    exact h.left,
  end,
  le_sup_right := begin
    assume p q : convergence_space X,
    assume l : filter X,
    assume x : X,
    assume h : (p ⊔ q).converges l x,
    exact h.right,
  end,
  sup_le := begin
    assume p q r : convergence_space X,
    assume le₁ : p ≤ r,
    assume le₂ : q ≤ r,
    assume ℱ : filter X,
    assume x : X,
    assume hr : r.converges ℱ x,
    have hp : p.converges ℱ x, from le₁ hr,
    have hq : q.converges ℱ x, from le₂ hr,
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
    assume h' : (Sup ps).converges ℱ x,
    exact h' h,
  end,
  Sup_le := begin
    assume ps : set (convergence_space X),
    assume q : convergence_space X,
    assume f : ∀ p : convergence_space X, p ∈ ps → p ≤ q,
    assume ℱ : filter X,
    assume x : X,
    assume h : q.converges ℱ x,
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
    assume h : p.converges ℱ x,
    exact or.inl h,
  end,
  inf_le_right := begin
    assume p q : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : q.converges ℱ x,
    exact or.inr h,
  end,
  le_inf := begin
    assume p q r : convergence_space X,
    assume le₁ : p ≤ q,
    assume le₂ : p ≤ r,
    assume l : filter X,
    assume x : X,
    assume h : (q ⊓ r).converges l x,
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
    assume h' : p.converges ℱ x,
    exact or.inr (exists.intro p (and.intro h h')),
  end,
  le_Inf := begin
    assume qs : set (convergence_space X),
    assume p : convergence_space X,
    assume f : ∀ q ∈ qs, p ≤ q,
    assume ℱ : filter X,
    assume x : X,
    assume h : (Inf qs).converges ℱ x,
    cases h,
      case or.inl : le₁ begin
        exact p.le_converges le₁ (p.pure_converges x)
      end,
      case or.inr : ex begin
        exact exists.elim ex begin
          assume q : convergence_space X,
          assume h' : q ∈ qs ∧ q.converges ℱ x,
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
    assume h : discrete.converges ℱ x,
    exact p.le_converges h (p.pure_converges x),
  end,
  bot_le := begin
    assume p : convergence_space X,
    assume ℱ : filter X,
    assume x : X,
    assume h : p.converges ℱ x,
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

def convergence_space.induced (f : X → Y) (q : convergence_space Y) : convergence_space X := {
  converges := λ ℱ x, q.converges (map f ℱ) (f x),
  pure_converges := by simp [filter.map_pure, pure_converges],
  le_converges := begin
    assume ℱ 𝒢 : filter X,
    assume le₁ : ℱ ≤ 𝒢,
    assume x : X,
    assume h : q.converges (map f 𝒢) (f x),
    have le₂ : map f ℱ ≤ map f 𝒢, apply map_mono le₁,
    apply q.le_converges le₂ h
  end,
}

inductive coinduced_converges (f : X → Y) (p : convergence_space X) (𝒢 : filter Y) (y : Y) : Prop
| pure_case (_ : 𝒢 ≤ pure y) : coinduced_converges
| other_case (ℱ : filter X) (x : X) (_ : 𝒢 ≤ map f ℱ) (_ : y = f x) (_ : p.converges ℱ x) : coinduced_converges

def convergence_space.coinduced (f : X → Y) (p : convergence_space X) : convergence_space Y := {
  converges := coinduced_converges f p,
  pure_converges := λ y, coinduced_converges.pure_case (le_refl (pure y)),
  le_converges := begin
    assume 𝒢₁ 𝒢₂ : filter Y,
    assume : 𝒢₁ ≤ 𝒢₂,
    assume y : Y,
    assume h : coinduced_converges f p 𝒢₂ y,
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
          (by assumption : p.converges ℱ x)
        end
  end,
}

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

instance {p : X → Prop} [q : convergence_space X] : convergence_space (subtype p) :=
convergence_space.induced coe q

instance {r : X → X → Prop} [q : convergence_space X] : convergence_space (quot r) :=
convergence_space.coinduced (quot.mk r) q

instance [p : convergence_space X] [q : convergence_space Y] : convergence_space (X × Y) :=
convergence_space.induced prod.fst p ⊓ convergence_space.induced prod.snd q

-------------------------------------------------------------------------------
-- Limits, adherence, open/closed, continuity
-------------------------------------------------------------------------------

def lim [p : convergence_space X] (ℱ : filter X) : set X := { x | p.converges ℱ x }

def adheres [p : convergence_space X] (ℱ : filter X) (x : X) : Prop :=
∃ 𝒢 ≤ ℱ, p.converges 𝒢 x

def adh [convergence_space X] (ℱ : filter X) : set X := { x | adheres ℱ x }

def is_open [p : convergence_space X] (A : set X) : Prop :=
∀ {ℱ} {x}, x ∈ A → p.converges ℱ x → A ∈ ℱ

def is_closed [p : convergence_space X] (A : set X) : Prop :=
∀ {ℱ} {x}, A ∈ ℱ → p.converges ℱ x → x ∈ A

structure continuous [p : convergence_space X] [q : convergence_space Y] (f : X → Y) : Prop :=
(filter_converges : ∀ {x} {ℱ}, p.converges ℱ x → q.converges (map f ℱ) (f x))

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

class hausdorff_space [convergence_space X] : Prop :=
(hausdorff_prop : ∀ (ℱ : filter X) [ne_bot ℱ], subsingleton (lim ℱ))
