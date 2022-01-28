import tactic
import order.filter.partial
import order.filter.ultrafilter
import algebra.support
import limit_space.basic

noncomputable theory
open set filter ultrafilter classical limit_space
open_locale classical filter

variables {X Y : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

@[ext] class pseudotopological_space (X : Type*) extends limit_space X :=
(ultra_converges : ∀ {x ℱ}, (∀ {𝒢 : ultrafilter X}, ↑𝒢 ≤ ℱ → converges 𝒢 x) -> converges ℱ x)

open pseudotopological_space

instance : has_coe (pseudotopological_space X) (limit_space X) := {
  coe := λ p, p.to_limit_space,
}
