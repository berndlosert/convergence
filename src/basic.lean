import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup

variables {a b : Type*}

class convergence_space (a : Type*) :=
(conv : filter a -> a -> Prop)
(pure_conv : forall {x : a}, conv (pure x) x)
(le_conv : forall {x : a} {l l' : filter a}, l <= l' -> conv l' x -> conv l x) -- l <= l' means l' ⊆ l

class kent_convergence_space (a : Type*) extends convergence_space a :=
(kent_conv : forall {x : a} {l : filter a}, conv l x -> conv (sup l (pure x)) x)

class limit_space (a : Type*) extends kent_convergence_space a :=
(sup_conv : forall {x : a} {l l' : filter a}, conv l x -> conv l' x -> conv (sup l l') x) -- l ⊔ l' means l ∩ l'

open convergence_space
open kent_convergence_space
open limit_space

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

def induced_kent (f : a -> b) [kent_convergence_space b] : kent_convergence_space a :=
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
    cases h with pure_case l x _ _ _,
    -- pure_case
    have : l1 <= pure y, from calc
      l1  <= l2     : (by assumption : l1 <= l2)
      ... <= pure y : pure_case,
    exact coinduced_conv.pure_case (by assumption : l1 <= pure y),
    -- other_case
    have : l1 <= map f l, from calc
      l1  <= l2      :  (by assumption : l1 <= l2)
      ... <= map f l :  (by assumption : l2 <= map f l),
    exact coinduced_conv.other_case l x
      (by assumption : l1 <= map f l)
      (by assumption : y = f x)
      (by assumption : conv l x)
  end,
}

lemma coinduced_def (f : a -> b) [convergence_space a] {l' : filter b} {y : b} :
  @convergence_space.conv b (coinduced f) l' y <-> coinduced_conv f l' y :=
iff.rfl

def coinduced_kent (f : a -> b) [kent_convergence_space a] : kent_convergence_space b :=
let coind := coinduced f in {
  kent_conv := begin
    assume y : b,
    assume l' : filter b,
    assume h : coinduced_conv f l' y,
    rw coinduced_def at *,
    cases h with pure_case l x _ _ _,
    -- case l' <= pure y
    have h' : sup l' (pure y) = pure y, from calc
      sup l' (pure y) = sup (pure y) l' : sup_comm
                  ... = pure y          : by rw sup_of_le_left pure_case,
    rw h',
    rw <- coinduced_def,
    apply @pure_conv b coind y,
    -- case l' <= map f l
    let l'' := sup l (pure x),
    have hlt : sup l' (pure y) <= map f l'', begin
      rw (by assumption : y = f x),
      have : l' <= sup (map f l) (pure (f x)),
        from le_sup_of_le_left (by assumption : l' <= map f l),
      simp,
      assumption,
    end,
    have hconv : conv l'' x, begin
      apply kent_conv,
      assumption
    end,
    apply coinduced_conv.other_case l'' x hlt (by assumption : y = f x) hconv
  end,
  ..coind
}

def lim [convergence_space a] (l : filter a) : set a := set_of (conv l)

structure continuous [convergence_space a] [convergence_space b] (f : a -> b) : Prop :=
(filter_conv : forall {x : a} {l : filter a}, conv l x -> conv (map f l) (f x))

class hausdorff_space [convergence_space a] : Prop :=
(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))
