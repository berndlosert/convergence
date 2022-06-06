import tactic
import order.filter.partial
import algebra.support
import kent_convergence_space.basic

noncomputable theory
open set filter classical kent_convergence_space
open_locale classical filter

variables {α β : Type*} 

/-!
### Definition
-/

@[ext] class limit_space (α : Type*) extends kent_convergence_space α :=
(sup_converges : ∀ {f g x}, converges f x -> converges g x -> converges (f ⊔ g) x) -- f ⊔ g means f ∩ g

open limit_space

instance : has_coe (limit_space α) (kent_convergence_space α) := 
{ coe := λ p, p.to_kent_convergence_space }

/-!
### Parital ordering
-/

instance : has_le (limit_space α) :=
⟨λ p q, p.to_convergence_space ≤ q.to_convergence_space⟩
