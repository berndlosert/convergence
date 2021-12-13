import order.filter.ultrafilter
import order.filter.partial
import algebra.support
import basic

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup

namespace convergence_space

variables {a b : Type*}

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

namespace kent_convergence_space

open convergence_space

variables {a b : Type*}

def induced_kent (f : a -> b) [inst : kent_convergence_space b] : kent_convergence_space a :=
let ind := induced f in {
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

def coinduced_kent (f : a -> b) [kent_convergence_space a] : kent_convergence_space b :=
let coind := coinduced f in {
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

namespace limit_space

open convergence_space
open kent_convergence_space

variables {a b : Type*}

def induced_limit (f : a -> b) [limit_space b] : limit_space a :=
let ind := induced_kent f in {
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
