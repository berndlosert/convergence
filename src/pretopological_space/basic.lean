import tactic
import order.filter.partial
import order.filter.ultrafilter
import algebra.support
import pseudotopological_space.basic

noncomputable theory
open set filter ultrafilter classical pseudotopological_space
open_locale classical filter

variables {α : Type*}

/-!
### Definition
-/

@[ext] class pretopological_space (α : Type*) extends pseudotopological_space α :=
(nhds_converges : ∀ x, converges (nhds x) x)

open pretopological_space

instance : has_coe (pretopological_space α) (pseudotopological_space α) := 
{ coe := λ p, p.to_pseudotopological_space }
