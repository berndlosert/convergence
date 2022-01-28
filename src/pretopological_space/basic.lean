import tactic
import order.filter.partial
import order.filter.ultrafilter
import algebra.support
import pseudotopological_space.basic

noncomputable theory
open set filter ultrafilter classical pseudotopological_space
open_locale classical filter

variables {X Y : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

@[ext] class pretopological_space (X : Type*) extends pseudotopological_space X :=
(nhds_converges : ∀ x, converges (nhds x) x)

attribute [ext] pretopological_space

open pretopological_space

instance : has_coe (pretopological_space X) (pseudotopological_space X) := {
  coe := λ p, p.to_pseudotopological_space,
}
