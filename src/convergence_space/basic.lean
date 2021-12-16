import tactic
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup has_inf has_mem

variables {a b : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

structure convergence_space (a : Type*) :=
(converges : filter a -> a -> Prop)
(pure_converges : forall x, converges (pure x) x)
(le_converges : forall {l l'}, l <= l' -> forall {x}, converges l' x -> converges l x) -- l <= l' means l' ⊆ l

attribute [ext] convergence_space
attribute [class] convergence_space

open convergence_space

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space a) := {
  le := fun p q, forall {l} {x}, q.converges l x -> p.converges l x
}

instance : partial_order (convergence_space a) := {
  le_refl := begin
    assume p : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : p.converges l x,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space a,
    assume le1 : p <= q,
    assume le2 : q <= r,
    assume l : filter a,
    assume x : a,
    assume h : r.converges l x,
    exact (le1 (le2 h))
  end,
  le_antisymm := begin
    assume p q : convergence_space a,
    assume le1 : p <= q,
    assume le2 : q <= p,
    ext l x,
    exact iff.intro le2 le1,
  end,
  ..convergence_space.has_le
}

-------------------------------------------------------------------------------
-- Discrete/indiscrete convergence spaces
-------------------------------------------------------------------------------

def discrete : convergence_space a := {
  converges := fun l x, true,
  pure_converges := by tauto,
  le_converges := by tauto,
}

def indiscrete : convergence_space a := {
  converges := fun l x, l <= pure x,
  pure_converges := by tauto,
  le_converges := by tauto,
}

instance : has_bot (convergence_space a) := {
  bot := discrete
}

instance : has_top (convergence_space a) := {
  top := indiscrete
}

-------------------------------------------------------------------------------
-- Supremum and infimum of convergence spaces
-------------------------------------------------------------------------------

instance : has_sup (convergence_space a) := {
  sup := fun p q, {
    converges := fun l x, and (p.converges l x) (q.converges l x),
    pure_converges := begin
      assume x : a,
      exact and.intro (p.pure_converges x) (q.pure_converges x),
    end,
    le_converges := begin
      assume l l' : filter a,
      assume h : l <= l',
      assume x : a,
      assume h' : and (p.converges l' x) (q.converges l' x),
      exact and.intro (p.le_converges h h'.left) (q.le_converges h h'.right)
    end,
  }
}

instance : has_Sup (convergence_space a) := {
  Sup := fun ps, {
    converges := fun l x, forall {p : convergence_space a}, mem p ps -> p.converges l x,
    pure_converges := begin
      assume x : a,
      assume p : convergence_space a,
      assume : mem p ps,
      exact p.pure_converges x,
    end,
    le_converges := begin
      assume l l' : filter a,
      assume h : l <= l',
      assume x : a,
      assume f : forall {p : convergence_space a}, mem p ps -> p.converges l' x,
      assume p : convergence_space a,
      assume h' : mem p ps,
      exact p.le_converges h (f h')
    end,
  }
}

instance : has_inf (convergence_space a) := {
  inf := fun p q, {
    converges := fun l x, or (p.converges l x) (q.converges l x),
    pure_converges := begin
      assume x : a,
      exact or.inl (p.pure_converges x),
    end,
    le_converges := begin
      assume l l' : filter a,
      assume h : l <= l',
      assume x : a,
      assume h' : or (p.converges l' x) (q.converges l' x),
      exact or.elim h'
        (assume hl, or.inl (p.le_converges h hl))
        (assume hr, or.inr (q.le_converges h hr))
    end,
  }
}

instance : has_Inf (convergence_space a) := {
  Inf := fun ps, {
    converges := fun l x, or
      (l <= pure x)
      (exists p : convergence_space a, and (mem p ps) (p.converges l x)),
    pure_converges := by tauto,
    le_converges := begin
      assume l l' : filter a,
      assume le1 : l <= l',
      assume x : a,
      assume h : or
        (l' <= pure x)
        (exists p : convergence_space a, and (mem p ps) (p.converges l' x)),
      cases h,
        case or.inl : le2 begin
          exact or.inl (le_trans le1 le2)
        end,
        case or.inr : ex begin
          exact exists.elim ex begin
            assume p h',
            exact or.inr (exists.intro p (and.intro h'.left (p.le_converges le1 h'.right)))
          end,
        end,
    end,
  }
}

-------------------------------------------------------------------------------
-- Lattice of convergence spaces
-------------------------------------------------------------------------------

instance : semilattice_sup (convergence_space a) := {
  le_sup_left := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : (sup p q).converges l x,
    exact h.left,
  end,
  le_sup_right := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : (sup p q).converges l x,
    exact h.right,
  end,
  sup_le := begin
    assume p q r : convergence_space a,
    assume le1 : p <= r,
    assume le2 : q <= r,
    assume l : filter a,
    assume x : a,
    assume hr : r.converges l x,
    have hp : p.converges l x, from le1 hr,
    have hq : q.converges l x, from le2 hr,
    exact and.intro hp hq
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_sup,
}

instance : semilattice_inf (convergence_space a) := {
  inf_le_left := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : p.converges l x,
    exact or.inl h,
  end,
  inf_le_right := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : q.converges l x,
    exact or.inr h,
  end,
  le_inf := begin
    assume p q r : convergence_space a,
    assume le1 : p <= q,
    assume le2 : p <= r,
    assume l : filter a,
    assume x : a,
    assume h : (inf q r).converges l x,
    cases h,
      exact le1 h,
      exact le2 h,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_inf,
}

instance : lattice (convergence_space a) := {
  ..convergence_space.semilattice_sup,
  ..convergence_space.semilattice_inf,
}

-------------------------------------------------------------------------------
-- Induced/coinduced convergence space
-------------------------------------------------------------------------------

def induced (f : a -> b) (q : convergence_space b) : convergence_space a := {
  converges := fun l x, q.converges (map f l) (f x),
  pure_converges := by simp [filter.map_pure, pure_converges],
  le_converges := begin
    assume l l' : filter a,
    assume le1 : l <= l',
    assume x : a,
    assume h : q.converges (map f l') (f x),
    have le2 : map f l <= map f l', apply map_mono le1,
    apply q.le_converges le2 h
  end,
}

inductive coinduced_converges (f : a -> b) (p : convergence_space a) (l' : filter b) (y : b) : Prop
| pure_case (_ : l' <= pure y) : coinduced_converges
| other_case (l : filter a) (x : a) (_ : l' <= map f l) (_ : y = f x) (_ : p.converges l x) : coinduced_converges

def coinduced (f : a -> b) (p : convergence_space a) : convergence_space b := {
  converges := coinduced_converges f p,
  pure_converges := fun y, coinduced_converges.pure_case (le_refl (pure y)),
  le_converges := begin
    assume l1 l2 : filter b,
    assume : l1 <= l2,
    assume y : b,
    assume h : coinduced_converges f p l2 y,
    cases h,
      case pure_case begin
        have : l1 <= pure y, from calc
          l1  <= l2     : (by assumption : l1 <= l2)
          ... <= pure y : (by assumption : l2 <= pure y),
        exact coinduced_converges.pure_case (by assumption : l1 <= pure y),
      end,
      case other_case : l x _ _ _ begin
        have : l1 <= map f l, from calc
          l1  <= l2      :  (by assumption : l1 <= l2)
          ... <= map f l :  (by assumption : l2 <= map f l),
        exact coinduced_converges.other_case l x
          (by assumption : l1 <= map f l)
          (by assumption : y = f x)
          (by assumption : p.converges l x)
        end
  end,
}

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

instance {p : a -> Prop} [q : convergence_space a] : convergence_space (subtype p) :=
induced coe q

instance {r : a -> a -> Prop} [q : convergence_space a] : convergence_space (quot r) :=
coinduced (quot.mk r) q

instance [p : convergence_space a] [q : convergence_space b] : convergence_space (prod a b) :=
inf (induced prod.fst p) (induced prod.snd q)

-------------------------------------------------------------------------------
-- Limits, adherence, open/closed, continuity
-------------------------------------------------------------------------------

def lim [p : convergence_space a] (l : filter a) : set a := set_of (p.converges l)

def adheres [p : convergence_space a] (l : filter a) (x : a) : Prop :=
exists l' <= l, p.converges l' x

def adh [convergence_space a] (l : filter a) : set a := set_of (adheres l)

def is_open [p : convergence_space a] (s : set a) : Prop :=
forall {l} {x}, mem x s -> p.converges l x -> mem s l

def is_closed [p : convergence_space a] (s : set a) : Prop :=
forall {l} {x}, mem s l -> p.converges l x -> mem x s

structure continuous [p : convergence_space a] [q : convergence_space b] (f : a -> b) : Prop :=
(filter_converges : forall {x} {l}, p.converges l x -> q.converges (map f l) (f x))

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

class hausdorff_space [convergence_space a] : Prop :=
(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))
