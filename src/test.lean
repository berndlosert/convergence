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
(sup_conv : forall {x : a} {l l' : filter a}, conv l x -> conv l' x -> conv (sup l l') x) -- l ⊔ l' means l ∩ l'

open convergence_space

def lim [convergence_space a] (l : filter a) : set a := set_of (conv l)

infix `converges_to`:100 := conv

structure continuous [convergence_space a] [convergence_space b] (f : a -> b) : Prop :=
(filter_conv : forall {x : a} {l : filter a}, l converges_to x -> map f l converges_to f x)

class hausdorff_space [convergence_space a] : Prop :=
(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))

def induced (f : a -> b) (t : convergence_space b) : convergence_space a := {
  conv := fun l x, map f l converges_to f x,
  pure_conv := by simp [filter.map_pure, pure_conv],
  le_conv := begin
    assume x : a,
    assume l l' : filter a,
    assume : l <= l',
    assume : map f l' converges_to f x,
    have : map f l <= map f l',
      apply map_mono (by assumption : l <= l'),
    apply le_conv
      (by assumption : map f l <= map f l')
      (by assumption : map f l' converges_to f x)
  end,
  sup_conv := begin
    assume x : a,
    assume l l' : filter a,
    assume : map f l converges_to f x,
    assume : map f l' converges_to f x,
    simp [map_sup],
    apply sup_conv
      (by assumption : map f l converges_to f x)
      (by assumption : map f l' converges_to f x)
  end
}

inductive coinduced_conv [convergence_space a] (f : a -> b) (l' : filter b) (y : b) : Prop
| pure_case (_ : l' <= pure y) : coinduced_conv
| other_case (l : filter a) (x : a) (_ : l' <= map f l) (_ : y = f x) (_ : conv l x) : coinduced_conv

def coinduced (f : a -> b) (t : convergence_space a) : convergence_space b := {
  conv := coinduced_conv f,
  pure_conv := fun y, coinduced_conv.pure_case (le_refl (pure y)),
  le_conv := begin
    assume y : b,
    assume l1 l2 : filter b,
    assume : l1 <= l2,
    assume h : coinduced_conv f l2 y,
    cases h with pure_case l x _ _ _,
    -- pure_case
    exact coinduced_conv.pure_case (trans (by assumption : l1 <= l2) pure_case),
    -- other_case
    exact coinduced_conv.other_case l x
      (trans (by assumption : l1 <= l2) (by assumption : l2 ≤ map f l))
      (by assumption : y = f x)
      (by assumption : conv l x)
  end,
  sup_conv := begin
    assume y : b,
    assume l1' l2' : filter b,
    assume h1 : coinduced_conv f l1' y,
    assume h2 : coinduced_conv f l2' y,
    cases h1 with pure_case1 l1 x1 _ _ _,
    cases h2 with pure_case2 l2 x2 _ _ _,
    -- case l1' <= pure y, l2' <= pure y
    exact coinduced_conv.pure_case
      (sup_le_iff.mpr
        (and.intro
	  (by assumption : l1' <= pure y)
	  (by assumption : l2' <= pure y))),
     -- case l1' ≤ pure y, l2' ≤ map f l2
     have : l1' <= map f (pure x2), begin
       rw map_pure f x2,
       rw <- (by assumption : y = f x2),
       exact pure_case1,
     end,
     let l : filter a := sup (pure x2) l2,
     have : sup l1' l2' <= map f l, begin
       exact sup_le_sup
         (by assumption : l1' <= map f (pure x2))
	 (by assumption : l2' <= map f l2),
     end,
     have : conv l x2, begin
       exact sup_conv
         pure_conv
	 (by assumption : conv l2 x2),
     end,
     exact coinduced_conv.other_case l x2
       (by assumption : sup l1' l2' <= map f l)
       (by assumption : y = f x2)
       (by assumption : conv l x2),
  end
}
