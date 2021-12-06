import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup

universes u v w
variables {α β : Type*}

class convergence_space (α : Type u) :=
(conv : filter α -> α -> Prop)
(pure_conv : forall {x : α}, conv (pure x) x)
(le_conv : forall {x : α} {l l' : filter α}, l <= l' -> conv l' x -> conv l x) -- l <= l' means l' ⊆ l
(sup_conv : forall {x : α} {l l' : filter α}, conv l x -> conv l' x -> conv (sup l l') x) -- l ⊔ l' means l ∩ l'

open convergence_space

def lim [convergence_space α] (l : filter α) : set α := set_of (conv l)

structure continuous [convergence_space α] [convergence_space β] (f : α -> β) : Prop :=
(filter_conv : forall {x : α} {l : filter α}, conv l x -> conv (map f l) (f x))

class hausdorff_space [convergence_space α] : Prop :=
(hausdorff_prop : forall (l : filter α) [ne_bot l], subsingleton (lim l))

def induced (f : α -> β) (t : convergence_space β) : convergence_space α := {
  conv := fun l x, conv (map f l) (f x),
  pure_conv := begin
    intro,
    simp [filter.map_pure],
    apply pure_conv
  end,
  le_conv := begin
    intros x l l' h₀ h₁,
    have h₂ : map f l <= map f l',
      apply map_mono h₀,
    apply le_conv h₂ h₁
  end,
  sup_conv := begin
    intros x l l' h₀ h₁,
    simp [map_sup],
    apply sup_conv h₀ h₁,
  end
}

/-
def coinduced (f : α -> β) (t : convergence_space α) : convergence_space β := {
  conv := fun l' y, l' <= pure y or (exists x l, l' <= map f l and y = f x and conv l x),
  pure_conv := begin
    intro,
    simp [and.left]
  end,
  le_conv := begin
    intros y l₁ l₂ h₀ h₁,
    exact or.elim h₁
      (assume h, or.inl (trans h₀ h))
      (assume h, match h with ⟨x, l, hm, hf, hc⟩ :=
        or.inr ⟨x, l, trans h₀ hm, hf, hc⟩
      end)
  end,
  sup_conv := begin
    intros y l₁ l₂ h₀ h₁,
    exact or.elim h₀
      (or.elim h₁
        (assume ha hb, or.inl (sup_le_iff.mpr ⟨hb, ha⟩))
	(assume ha hb, _))
      (or.elim h₁ sorry sorry)
    --  (or.elim h₁
    --    (assume ha hb, or.inl (sup_lt_iff.mpr (ha, hb)))
    --    _)
    --  (or.elim h₁ _ _)
  end
}
-/
