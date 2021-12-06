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
    exact coinduced_conv.pure_case (trans (by assumption : l1 <= l2) pure_case),
    exact coinduced_conv.other_case l x
      (trans (by assumption : l1 <= l2) (by assumption : l2 ≤ map f l))
      (by assumption : y = f x)
      (by assumption : conv l x)
  end,
  sup_conv := sorry,
}

/-
def coinduced (f : a -> b) (t : convergence_space a) : convergence_space b := {
  conv := fun l' y, (l' <= pure y) \/ (exists x l, l' <= map f l /\ y = f x /\ conv l x),
  pure_conv := begin
    intro,
    simp [and.left]
  end,
  le_conv := begin
    intros y l1 l2 h0 h1,
    exact or.elim h1
      (assume h, or.inl (trans h0 h))
      (assume h, match h with ⟨x, l, hm, hf, hc⟩ :=
        or.inr ⟨x, l, trans h0 hm, hf, hc⟩
      end)
  end,
  sup_conv := begin
    intros y l1 l2 h0 h1,
    exact or.elim h0
      (or.elim h1
        (assume ha hb, or.inl (sup_le_iff.mpr ⟨hb, ha⟩))
	(assume ha hb, sorry))
      (or.elim h1 sorry sorry)
    --  (or.elim h1
    --    (assume ha hb, or.inl (sup_lt_iff.mpr (ha, hb)))
    --    _)
    --  (or.elim h1 _ _)
  end
}
-/
