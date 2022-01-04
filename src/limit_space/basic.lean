import tactic
import order.filter.partial
import algebra.support
import kent_convergence_space.basic

noncomputable theory
open set filter classical
open_locale classical filter

variables {X Y : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

structure limit_space (X : Type*) extends kent_convergence_space X :=
(sup_converges : ∀ {x ℱ 𝒢}, converges ℱ x -> converges 𝒢 x -> converges (ℱ ⊔ 𝒢) x) -- ℱ ⊔ 𝒢 means ℱ ∩ 𝒢

attribute [ext] limit_space
attribute [class] limit_space

open limit_space

instance : has_coe (limit_space X) (kent_convergence_space X) := {
  coe := λ p, p.to_kent_convergence_space,
}
