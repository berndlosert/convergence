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
(conv : filter a -> a -> Prop)
(pure_conv : forall x, conv (pure x) x)
(le_conv : forall {x} {l l'}, l <= l' -> conv l' x -> conv l x) -- l <= l' means l' ⊆ l

attribute [ext] convergence_space
attribute [class] convergence_space

open convergence_space

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space a) := {
  le := fun p q, forall {l} {x}, q.conv l x -> p.conv l x
}

instance : partial_order (convergence_space a) := {
  le_refl := begin
    assume p : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : p.conv l x,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space a,
    assume le1 : p <= q,
    assume le2 : q <= r,
    assume l : filter a,
    assume x : a,
    assume h : r.conv l x,
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
  conv := fun l x, true,
  pure_conv := by tauto,
  le_conv := by tauto,
}

def indiscrete : convergence_space a := {
  conv := fun l x, l <= pure x,
  pure_conv := by tauto,
  le_conv := by tauto,
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
    conv := fun l x, and (p.conv l x) (q.conv l x),
    pure_conv := begin
      assume x : a,
      exact and.intro (p.pure_conv x) (q.pure_conv x),
    end,
    le_conv := begin
      assume x : a,
      assume l l' : filter a,
      assume h : l <= l',
      assume h' : and (p.conv l' x) (q.conv l' x),
      exact and.intro (p.le_conv h h'.left) (q.le_conv h h'.right)
    end,
  }
}

instance : has_Sup (convergence_space a) := {
  Sup := fun ps, {
    conv := fun l x, forall {p : convergence_space a}, mem p ps -> p.conv l x,
    pure_conv := begin
      assume x : a,
      assume p : convergence_space a,
      assume : mem p ps,
      exact p.pure_conv x,
    end,
    le_conv := begin
      assume x : a,
      assume l l' : filter a,
      assume h : l <= l',
      assume f : forall {p : convergence_space a}, mem p ps -> p.conv l' x,
      assume p : convergence_space a,
      assume h' : mem p ps,
      exact p.le_conv h (f h')
    end,
  }
}

instance : has_inf (convergence_space a) := {
  inf := fun p q, {
    conv := fun l x, or (p.conv l x) (q.conv l x),
    pure_conv := begin
      assume x : a,
      exact or.inl (p.pure_conv x),
    end,
    le_conv := begin
      assume x : a,
      assume l l' : filter a,
      assume h : l <= l',
      assume h' : or (p.conv l' x) (q.conv l' x),
      exact or.elim h'
        (assume hl, or.inl (p.le_conv h hl))
        (assume hr, or.inr (q.le_conv h hr))
    end,
  }
}

-- TODO: has_Inf

-------------------------------------------------------------------------------
-- Lattice of convergence spaces
-------------------------------------------------------------------------------

instance : semilattice_sup (convergence_space a) := {
  le_sup_left := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : (sup p q).conv l x,
    exact h.left,
  end,
  le_sup_right := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : (sup p q).conv l x,
    exact h.right,
  end,
  sup_le := begin
    assume p q r : convergence_space a,
    assume le1 : p <= r,
    assume le2 : q <= r,
    assume l : filter a,
    assume x : a,
    assume hr : r.conv l x,
    have hp : p.conv l x, from le1 hr,
    have hq : q.conv l x, from le2 hr,
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
    assume h : p.conv l x,
    exact or.inl h,
  end,
  inf_le_right := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : q.conv l x,
    exact or.inr h,
  end,
  le_inf := begin
    assume p q r : convergence_space a,
    assume le1 : p <= q,
    assume le2 : p <= r,
    assume l : filter a,
    assume x : a,
    assume h : (inf q r).conv l x,
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
  conv := fun l x, q.conv (map f l) (f x),
  pure_conv := by simp [filter.map_pure, pure_conv],
  le_conv := begin
    assume x : a,
    assume l l' : filter a,
    assume le1 : l <= l',
    assume h : q.conv (map f l') (f x),
    have le2 : map f l <= map f l', apply map_mono le1,
    apply q.le_conv le2 h
  end,
}

inductive coinduced_conv (f : a -> b) (p : convergence_space a) (l' : filter b) (y : b) : Prop
| pure_case (_ : l' <= pure y) : coinduced_conv
| other_case (l : filter a) (x : a) (_ : l' <= map f l) (_ : y = f x) (_ : p.conv l x) : coinduced_conv

def coinduced (f : a -> b) (p : convergence_space a) : convergence_space b := {
  conv := coinduced_conv f p,
  pure_conv := fun y, coinduced_conv.pure_case (le_refl (pure y)),
  le_conv := begin
    assume y : b,
    assume l1 l2 : filter b,
    assume : l1 <= l2,
    assume h : coinduced_conv f p l2 y,
    cases h,
      case pure_case begin
        have : l1 <= pure y, from calc
          l1  <= l2     : (by assumption : l1 <= l2)
          ... <= pure y : (by assumption : l2 <= pure y),
        exact coinduced_conv.pure_case (by assumption : l1 <= pure y),
      end,
      case other_case : l x _ _ _ begin
        have : l1 <= map f l, from calc
          l1  <= l2      :  (by assumption : l1 <= l2)
          ... <= map f l :  (by assumption : l2 <= map f l),
        exact coinduced_conv.other_case l x
          (by assumption : l1 <= map f l)
          (by assumption : y = f x)
          (by assumption : p.conv l x)
        end
  end,
}

---------------------------------------------------------------------------------
---- Induced/coinduced Kent convergence space
---------------------------------------------------------------------------------
--
--namespace kent_convergence_space
--
--open convergence_space
--
--def induced (f : a -> b) [inst : kent_convergence_space b] : kent_convergence_space a :=
--let ind := convergence_space.induced f in {
--  kent_conv :=
--    begin
--      assume x : a,
--      assume l : filter a,
--      let l' := map f l,
--      let y := f x,
--      assume h : conv l' y,
--      rw induced_def at *,
--      simp [kent_conv h],
--    end,
--  ..ind
--}
--
--def coinduced (f : a -> b) [kent_convergence_space a] : kent_convergence_space b :=
--let coind := convergence_space.coinduced f in {
--  kent_conv := begin
--    assume y : b,
--    assume l' : filter b,
--    assume h : coinduced_conv f l' y,
--    rw coinduced_def at *,
--    cases h,
--      case pure_case begin
--        have : sup l' (pure y) = pure y, from calc
--          sup l' (pure y) = sup (pure y) l' : sup_comm
--                      ... = pure y          : by rw sup_of_le_left h,
--        have : coinduced_conv f (pure y) y, from @pure_conv b coind y,
--        show coinduced_conv f (sup l' (pure y)) y, begin
--          rw (by assumption : sup l' (pure y) = pure y),
--          assumption,
--        end,
--      end,
--      case other_case : l x _ _ _ begin
--        let l'' := sup l (pure x),
--        have : sup l' (pure y) <= map f l'', from calc
--          sup l' (pure y) <= sup (map f l) (pure y)         : sup_le_sup_right (by assumption : l' <= map f l) (pure y)
--                      ...  = sup (map f l) (pure (f x))     : by rw (by assumption : y = f x)
--                      ...  = sup (map f l) (map f (pure x)) : by rw filter.map_pure
--                      ...  = map f (sup l (pure x))         : map_sup,
--        have : conv l'' x, begin
--          apply kent_conv,
--          assumption
--        end,
--        apply coinduced_conv.other_case l'' x
--          (by assumption : sup l' (pure y) <= map f l'')
--          (by assumption : y = f x)
--          (by assumption : conv l'' x)
--      end,
--  end,
--  ..coind
--}
--
--end kent_convergence_space
--
---------------------------------------------------------------------------------
---- Induced/coinduced limit space
---------------------------------------------------------------------------------
--
--namespace limit_space
--
--open convergence_space
--open kent_convergence_space
--
--def induced (f : a -> b) [limit_space b] : limit_space a :=
--let ind := kent_convergence_space.induced f in {
--  sup_conv := begin
--    assume x : a,
--    assume l l' : filter a,
--    assume : conv (map f l) (f x),
--    assume : conv (map f l') (f x),
--    rw induced_def at *,
--    simp [map_sup],
--    apply sup_conv
--      (by assumption : conv (map f l) (f x))
--      (by assumption : conv (map f l') (f x))
--  end,
--  ..ind
--}
--
--end limit_space
--
---------------------------------------------------------------------------------
---- Convergence spaces constructions
---------------------------------------------------------------------------------
--
--namespace convergence_space
--
--instance {p : a -> Prop} [q : convergence_space a] : convergence_space (subtype p) :=
--@induced _ _ coe q
--
--instance {r : a -> a -> Prop} [q : convergence_space a] : convergence_space (quot r) :=
--@coinduced _ _ (quot.mk r) q
--
----instance [p : convergence_space a] [q : convergence_space b] : convergence_space (prod a b) :=
----inf (@induced _ _ prod.fst p) (@induced _ _ prod.snd q)
--
--end convergence_space
--
---------------------------------------------------------------------------------
---- Limits, adherence, open/closed, continuity
---------------------------------------------------------------------------------
--
--def lim [convergence_space a] (l : filter a) : set a := set_of (conv l)
--
--def adheres [convergence_space a] (l : filter a) (x : a) : Prop :=
--exists l' <= l, conv l' x
--
--def adh [convergence_space a] (l : filter a) : set a := set_of (adheres l)
--
--def is_open [convergence_space a] (s : set a) : Prop :=
--forall {l : filter a} {x : a}, mem x s -> conv l x -> mem s l
--
--def is_closed [convergence_space a] (s : set a) : Prop :=
--forall {l : filter a} {x : a}, mem s l -> conv l x -> mem x s
--
--structure continuous [convergence_space a] [convergence_space b] (f : a -> b) : Prop :=
--(filter_conv : forall {x : a} {l : filter a}, conv l x -> conv (map f l) (f x))
--
---------------------------------------------------------------------------------
---- Misc.
---------------------------------------------------------------------------------
--
--class hausdorff_space [convergence_space a] : Prop :=
--(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))
