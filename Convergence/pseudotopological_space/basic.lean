import tactic
import order.filter.partial
import order.filter.ultrafilter
import algebra.support
import limit_space.basic

noncomputable theory
open set filter ultrafilter classical limit_space
open_locale classical filter

variables {α β : Type*}

/-!
### Definition
-/

@[ext] class pseudotopological_space (α : Type*) extends limit_space α :=
(ultra_converges : ∀ {f x}, (∀ {g : ultrafilter α}, ↑g ≤ f → converges g x) -> converges f x)

open pseudotopological_space

namespace pseudotopological_space

instance : has_coe (pseudotopological_space α) (limit_space α) := 
{ coe := λ p, p.to_limit_space }

end pseudotopological_space