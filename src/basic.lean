import tactic
import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup has_inf has_mem

variables {a b : Type*}

-------------------------------------------------------------------------------
-- Definition of convergence space and specializations thereof
-------------------------------------------------------------------------------

class convergence_space (a : Type*) :=
(conv : filter a -> a -> Prop)
(pure_conv : forall {x : a}, conv (pure x) x)
(le_conv : forall {x : a} {l l' : filter a}, l <= l' -> conv l' x -> conv l x) -- l <= l' means l' ⊆ l

attribute [ext] convergence_space

class kent_convergence_space (a : Type*) extends convergence_space a :=
(kent_conv : forall {x : a} {l : filter a}, conv l x -> conv (sup l (pure x)) x)

class limit_space (a : Type*) extends kent_convergence_space a :=
(sup_conv : forall {x : a} {l l' : filter a}, conv l x -> conv l' x -> conv (sup l l') x) -- l ⊔ l' means l ∩ l'

class pseudotopological_space (a : Type*) extends limit_space a :=
(ultra_conv : forall {x : a} {l : filter a}, (forall {u : ultrafilter a}, conv u.to_filter x) -> conv l x)

open convergence_space kent_convergence_space limit_space

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

namespace convergence_space

instance : has_le (convergence_space a) := {
  le := fun p q, forall {l : filter a} {x : a}, @conv a q l x -> @conv a p l x
}

instance : partial_order (convergence_space a) := {
  le_refl := begin
    assume p : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : @conv a p l x,
    exact h,
  end,
  le_trans := begin
    assume p q r : convergence_space a,
    assume le1 : p <= q,
    assume le2 : q <= r,
    assume l : filter a,
    assume x : a,
    assume h : @conv a r l x,
    exact (@le1 l x (@le2 l x h))
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

end convergence_space

-------------------------------------------------------------------------------
-- Discrete/indiscrete convergence spaces
-------------------------------------------------------------------------------

namespace convergence_space

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

end convergence_space

-------------------------------------------------------------------------------
-- Supremum and infimum of convergence spaces
-------------------------------------------------------------------------------

namespace convergence_space

instance : has_sup (convergence_space a) := {
  sup := fun p q, {
    conv := fun l x, and (@conv a p l x) (@conv a q l x),
    pure_conv := begin
      assume x : a,
      exact and.intro (@pure_conv a p x) (@pure_conv a q x),
    end,
    le_conv := begin
      assume x : a,
      assume l l' : filter a,
      assume h : l <= l',
      assume h' : and (@conv a p l' x) (@conv a q l' x),
      exact and.intro (@le_conv a p x l l' h h'.left) (@le_conv a q x l l' h h'.right)
    end,
  }
}

instance : has_inf (convergence_space a) := {
  inf := fun p q, {
    conv := fun l x, or (@conv a p l x) (@conv a q l x),
    pure_conv := begin
      assume x : a,
      exact or.inl (@pure_conv a p x),
    end,
    le_conv := begin
      assume x : a,
      assume l l' : filter a,
      assume h : l <= l',
      assume h' : or (@conv a p l' x) (@conv a q l' x),
      exact or.elim h'
        (assume hl, or.inl (@le_conv a p x l l' h hl))
        (assume hr, or.inr (@le_conv a q x l l' h hr))
    end,
  }
}

end convergence_space

-------------------------------------------------------------------------------
-- Lattice of convergence spaces
-------------------------------------------------------------------------------

namespace convergence_space

instance : semilattice_sup (convergence_space a) := {
  le_sup_left := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : @conv a (sup p q) l x,
    exact h.left,
  end,
  le_sup_right := begin
    assume p q : convergence_space a,
    assume l : filter a,
    assume x : a,
    assume h : @conv a (sup p q) l x,
    exact h.right,
  end,
  sup_le := begin
    assume p q r : convergence_space a,
    assume le1 : p <= r,
    assume le2 : q <= r,
    assume l : filter a,
    assume x : a,
    assume hr : @conv a r l x,
    have hp : @conv a p l x, from @le1 l x hr,
    have hq : @conv a q l x, from @le2 l x hr,
    exact and.intro hp hq
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_sup,
}

end convergence_space

-------------------------------------------------------------------------------
-- Induced/coinduced convergence space
-------------------------------------------------------------------------------

namespace convergence_space

def induced (f : a -> b) [convergence_space b] : convergence_space a := {
  conv := fun l x, conv (map f l) (f x),
  pure_conv := by simp [filter.map_pure, pure_conv],
  le_conv := begin
    assume x : a,
    assume l l' : filter a,
    assume : l <= l',
    assume : conv (map f l') (f x),
    have : map f l <= map f l',
      apply map_mono (by assumption : l <= l'),
    apply le_conv
      (by assumption : map f l <= map f l')
      (by assumption : conv (map f l') (f x))
  end,
}

lemma induced_def (f : a -> b) [convergence_space b] {l : filter a} {x : a} :
  @convergence_space.conv a (induced f) l x <-> conv (map f l) (f x) :=
iff.rfl

inductive coinduced_conv [convergence_space a] (f : a -> b) (l' : filter b) (y : b) : Prop
| pure_case (_ : l' <= pure y) : coinduced_conv
| other_case (l : filter a) (x : a) (_ : l' <= map f l) (_ : y = f x) (_ : conv l x) : coinduced_conv

def coinduced (f : a -> b) [convergence_space a] : convergence_space b := {
  conv := coinduced_conv f,
  pure_conv := fun y, coinduced_conv.pure_case (le_refl (pure y)),
  le_conv := begin
    assume y : b,
    assume l1 l2 : filter b,
    assume : l1 <= l2,
    assume h : coinduced_conv f l2 y,
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
          (by assumption : conv l x)
        end
  end,
}

lemma coinduced_def (f : a -> b) [convergence_space a] {l' : filter b} {y : b} :
  @convergence_space.conv b (coinduced f) l' y <-> coinduced_conv f l' y :=
iff.rfl

end convergence_space

-------------------------------------------------------------------------------
-- Induced/coinduced Kent convergence space
-------------------------------------------------------------------------------

namespace kent_convergence_space

open convergence_space

def induced (f : a -> b) [inst : kent_convergence_space b] : kent_convergence_space a :=
let ind := convergence_space.induced f in {
  kent_conv :=
    begin
      assume x : a,
      assume l : filter a,
      let l' := map f l,
      let y := f x,
      assume h : conv l' y,
      rw induced_def at *,
      simp [kent_conv h],
    end,
  ..ind
}

def coinduced (f : a -> b) [kent_convergence_space a] : kent_convergence_space b :=
let coind := convergence_space.coinduced f in {
  kent_conv := begin
    assume y : b,
    assume l' : filter b,
    assume h : coinduced_conv f l' y,
    rw coinduced_def at *,
    cases h,
      case pure_case begin
        have : sup l' (pure y) = pure y, from calc
          sup l' (pure y) = sup (pure y) l' : sup_comm
                      ... = pure y          : by rw sup_of_le_left h,
        have : coinduced_conv f (pure y) y, from @pure_conv b coind y,
        show coinduced_conv f (sup l' (pure y)) y, begin
          rw (by assumption : sup l' (pure y) = pure y),
          assumption,
        end,
      end,
      case other_case : l x _ _ _ begin
        let l'' := sup l (pure x),
        have : sup l' (pure y) <= map f l'', from calc
          sup l' (pure y) <= sup (map f l) (pure y)         : sup_le_sup_right (by assumption : l' <= map f l) (pure y)
                      ...  = sup (map f l) (pure (f x))     : by rw (by assumption : y = f x)
                      ...  = sup (map f l) (map f (pure x)) : by rw filter.map_pure
                      ...  = map f (sup l (pure x))         : map_sup,
        have : conv l'' x, begin
          apply kent_conv,
          assumption
        end,
        apply coinduced_conv.other_case l'' x
          (by assumption : sup l' (pure y) <= map f l'')
          (by assumption : y = f x)
          (by assumption : conv l'' x)
      end,
  end,
  ..coind
}

end kent_convergence_space

-------------------------------------------------------------------------------
-- Induced/coinduced limit space
-------------------------------------------------------------------------------

namespace limit_space

open convergence_space
open kent_convergence_space

def induced (f : a -> b) [limit_space b] : limit_space a :=
let ind := kent_convergence_space.induced f in {
  sup_conv := begin
    assume x : a,
    assume l l' : filter a,
    assume : conv (map f l) (f x),
    assume : conv (map f l') (f x),
    rw induced_def at *,
    simp [map_sup],
    apply sup_conv
      (by assumption : conv (map f l) (f x))
      (by assumption : conv (map f l') (f x))
  end,
  ..ind
}

end limit_space

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

namespace convergence_space

instance {p : a -> Prop} [q : convergence_space a] : convergence_space (subtype p) :=
@induced _ _ coe q

instance {r : a -> a -> Prop} [q : convergence_space a] : convergence_space (quot r) :=
@coinduced _ _ (quot.mk r) q

--instance [p : convergence_space a] [q : convergence_space b] : convergence_space (prod a b) :=
--inf (@induced _ _ prod.fst p) (@induced _ _ prod.snd q)

end convergence_space

-------------------------------------------------------------------------------
-- Limits, adherence, open/closed, continuity
-------------------------------------------------------------------------------

def lim [convergence_space a] (l : filter a) : set a := set_of (conv l)

def adheres [convergence_space a] (l : filter a) (x : a) : Prop :=
exists l' <= l, conv l' x

def adh [convergence_space a] (l : filter a) : set a := set_of (adheres l)

def is_open [convergence_space a] (s : set a) : Prop :=
forall {l : filter a} {x : a}, mem x s -> conv l x -> mem s l

def is_closed [convergence_space a] (s : set a) : Prop :=
forall {l : filter a} {x : a}, mem s l -> conv l x -> mem x s

structure continuous [convergence_space a] [convergence_space b] (f : a -> b) : Prop :=
(filter_conv : forall {x : a} {l : filter a}, conv l x -> conv (map f l) (f x))

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

class hausdorff_space [convergence_space a] : Prop :=
(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))
