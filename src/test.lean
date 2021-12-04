import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w

def dot {α : Type u} (x : α) : filter α := principal {x}

lemma map_dot {α : Type u} {β : Type v} {x : α} {f : α → β} : map f (dot x) = dot (f x) :=
by simp [dot]

class convergence_space (α : Type u) :=
(conv       : filter α → α → Prop)
(dot_conv  : ∀ {x : α}, conv (dot x) x)
(le_conv   : ∀ {x : α} {F G : filter α}, F ≤ G → conv F x → conv G x)
(sup_conv  : ∀ {x : α} {F G : filter α}, conv F x → conv G x → conv (F ⊔ G) x)

open convergence_space

def lim {α : Type u} [convergence_space α] (F : filter α) : set α := set_of (conv F)

structure continuous {α β : Type*} (f : α → β) [convergence_space α] [convergence_space β] : Prop :=
(filter_conv : ∀ {x : α} {F : filter α}, conv F x → conv (map f F) (f x))

class hausdorff_space (α : Type u) [convergence_space α] : Prop :=
(hausdorff_pred : ∀ (F : filter α), subsingleton (lim F))

def induced {α : Type u} {β : Type v} (f : α → β) (t : convergence_space β) : convergence_space α := {
  conv := λ F x, conv (map f F) (f x),
  dot_conv := begin
    intro,
    simp [map_dot],
    apply dot_conv
  end,
  le_conv := begin
    assume x : α,
    assume F G : filter α,
    assume h0 : F ≤ G,
    assume h1 : conv (map f F) (f x),
    have h : map f F ≤ map f G, apply map_mono h0,
    apply le_conv h h1
  end,
  sup_conv := begin
    intros x F G h0 h1,
    simp [map_sup],
    apply sup_conv h0 h1
  end
}
