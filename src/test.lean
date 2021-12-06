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

structure continuous [convergence_space a] [convergence_space b] (f : a -> b) : Prop :=
(filter_conv : forall {x : a} {l : filter a}, conv l x -> conv (map f l) (f x))

class hausdorff_space [convergence_space a] : Prop :=
(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))

def induced (f : a -> b) (t : convergence_space b) : convergence_space a := {
  conv := fun l x, conv (map f l) (f x),
  pure_conv := begin
    intro,
    simp [filter.map_pure],
    apply pure_conv
  end,
  le_conv := begin
    intros x l l' h0 h1,
    have h2 : map f l <= map f l',
      apply map_mono h0,
    apply le_conv h2 h1
  end,
  sup_conv := begin
    intros x l l' h0 h1,
    simp [map_sup],
    apply sup_conv h0 h1,
  end
}

inductive coinduced_conv (f : a -> b) (l' : filter b) (y : b) : Prop
| pure_case (hp : l' <= pure y) : coinduced_conv
| impure_case [convergence_space a] (l : filter a) (x : a) (hlt : l' <= map f l) (hfx : y = f x) (hconv : conv l x) : coinduced_conv

def coinduced (f : a -> b) (t : convergence_space a) : convergence_space b := {
  conv := coinduced_conv f,
  pure_conv := fun y, coinduced_conv.pure_case (le_refl (pure y)),
  le_conv := sorry,
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
