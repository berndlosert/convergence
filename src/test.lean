import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w

def dot {α : Type u} (x : α) : filter α := principal {x}

class convergence_space (α : Type u) :=
(lim        : filter α → set α)
(dot_conv    : ∀ (x : α), x ∈ lim (dot x))
(subfil_conv : ∀ (x : α) (F G : filter α), F ≤ G ∧ x ∈ lim F → x ∈ lim G)
(inter_conv  : ∀ (x : α) (F G : filter α), x ∈ lim F → x ∈ lim (F ⊓ dot x))

open convergence_space

structure continuous {α β : Type*} (f : α → β) [convergence_space α] [convergence_space β] : Prop :=
(filter_conv : ∀ (x : α) (F : filter α), x ∈ lim F → f x ∈ lim (map f F))
