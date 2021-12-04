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
(lim       : filter α → α → Prop)
(dot_conv  : ∀ {x : α}, lim (dot x) x)
(le_conv   : ∀ {x : α} {F G : filter α}, F ≤ G → lim F x → lim G x)
(sup_conv  : ∀ {x : α} {F G : filter α} (h0 : lim F x) (h1 : lim G x), lim (F ⊔ G) x)

open convergence_space

structure continuous {α β : Type*} (f : α → β) [convergence_space α] [convergence_space β] : Prop :=
(filter_conv : ∀ (F : filter α), image f (lim F) ⊆ lim (map f F))

class hausdorff_space (α : Type u) [convergence_space α] : Prop :=
(limit_subsingl : ∀ (F : filter α), subsingleton (set_of (lim F)))

def induced {α : Type u} {β : Type v} (f : α → β) (t : convergence_space β) : convergence_space α := {
  lim := λ F x, lim (map f F) (f x),
  dot_conv := begin
    intro,
    simp [map_dot],
    apply dot_conv
  end,
  le_conv := begin
    assume x : α,
    assume F G : filter α,
    assume h0 : F ≤ G,
    assume h1 : lim (map f F) (f x),
    have h : map f F ≤ map f G, apply map_mono h0,
    apply le_conv h h1
  end,
  sup_conv := begin
    intros,
    simp [map_sup],
    apply sup_conv h0 h1
  end
}
