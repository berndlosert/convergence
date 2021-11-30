import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter

universes u v w

def dot {α : Type u} (x : α) : filter α := principal {x}

class convergence_space (α : Type u) :=
(lim         : filter α → α → Prop)
/-
(dot_conv    : ∀ (x : α), x ∈ lim (dot x))
(inter_conv  : ∀ (x : α) (F : filter α), lim F ⊆ lim (F ⊓ dot x))
(subfil_conv : ∀ (F G : filter α), F ≤ G → lim F ⊆ lim G)
-/

open convergence_space

structure continuous {α β : Type*} (f : α → β) [convergence_space α] [convergence_space β] : Prop :=
(filter_conv : ∀ (F : filter α), image f (lim F) ⊆ lim (map f F))

class hausdorff_space (α : Type u) [convergence_space α] : Prop :=
(limit_subsingl : ∀ (F : filter α), subsingleton (set_of (lim F)))

def subspace {α : Type u} {s : set α} [c : convergence_space α] : convergence_space (subtype s) :=
convergence_space.mk (λ F x, @convergence_space.lim α c (map coe F) x)

