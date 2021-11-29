import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w

def dot {α : Type u} (x : α) : filter α := principal {x}

class convergence_space (α : Type u) :=
(conv        : filter α → α → Prop)
(dot_conv    : ∀ (x : α), conv (dot x) x)
(subfil_conv : ∀ (x : α) (F G : filter α), F ≤ G ∧ conv F x → conv G x)
(inter_conv  : ∀ (x : α) (F G : filter α), conv F x → conv (F ⊓ dot x) x)

open convergence_space

structure continuous {α β : Type*} (f : α → β) [cp1 : convergence_space α] [cp2 : convergence_space β] : Prop :=
(filter_conv : ∀ (F : filter α) (x : α), conv F x → conv (map f F) (f x))
