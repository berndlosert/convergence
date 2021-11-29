import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w

def dot {α : Type u} (x : α) : filter α := principal {x}

structure convergence_space (α : Type u) :=
(conv           : filter α → α → Prop)
(dot_conv       : ∀ (x : α), conv (dot x) x)
(subfil_conv    : ∀ (x : α) (f g : filter α), f ≤ g ∧ conv f x → conv g x)
(inter_conv     : ∀ (x : α) (f g : filter α), conv f x → conv (f ⊓ dot x) x)
