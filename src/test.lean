import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w
variables {α β : Type*}

def dot (x : α) : filter α := principal {x}

lemma map_dot {x : α} {f : α → β} : map f (dot x) = dot (f x) :=
by simp [dot]

class convergence_space (α : Type u) :=
(conv : filter α → α → Prop)
(dot_conv : ∀ {x : α}, conv (dot x) x)
(le_conv : ∀ {x : α} {l l' : filter α}, l ≤ l' → conv l x → conv l' x)
(sup_conv : ∀ {x : α} {l l' : filter α}, conv l x → conv l' x → conv (l ⊔ l') x)

open convergence_space

def lim [convergence_space α] (l : filter α) : set α := set_of (conv l)

structure continuous [convergence_space α] [convergence_space β] (f : α → β) : Prop :=
(filter_conv : ∀ {x : α} {l : filter α}, conv l x → conv (map f l) (f x))

class hausdorff_space [convergence_space α] : Prop :=
(hausdorff_pred : ∀ (l : filter α), subsingleton (lim l))

def induced (f : α → β) (t : convergence_space β) : convergence_space α := {
  conv := λ l x, conv (map f l) (f x),
  dot_conv := begin
    intro,
    simp [map_dot],
    apply dot_conv
  end,
  le_conv := begin
    assume x : α,
    assume l l' : filter α,
    assume h₀ : l ≤ l',
    assume h₁ : conv (map f l) (f x),
    have h₂ : map f l ≤ map f l', apply map_mono h₀,
    apply le_conv h₂ h₁
  end,
  sup_conv := begin
    intros x l l' h₀ h₁,
    simp [map_sup],
    apply sup_conv h₀ h₁
  end
}

def coinduced (f : α → β) (t : convergence_space α) : convergence_space β := {
  conv := λ l' y, l' = dot y ∨ ∃ x l, l' = map f l ∧ y = f x ∧ conv l x,
  dot_conv := sorry,
  le_conv := sorry,
  sup_conv := sorry
}
