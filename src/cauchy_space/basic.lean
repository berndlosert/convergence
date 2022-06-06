import tactic
import order.filter.partial
import order.filter.ultrafilter
import algebra.support
import limit_space.basic

noncomputable theory
open set filter ultrafilter classical convergence_space limit_space
open_locale classical filter

variables {α β : Type*}

/-!
### Definition
-/

/-- A Cauchy structure on `α`. -/
@[ext] class cauchy_space (α : Type*) :=
(cauchy : filter α → Prop)
(pure_cauchy : ∀ x, cauchy (pure x))
(le_cauchy : ∀ {f g}, f ≤ g → cauchy g → cauchy f)
(inf_sup_cauchy: ∀ {f g}, cauchy f → cauchy g → ne_bot (f ⊓ g) → cauchy (f ⊔ g))

open cauchy_space

instance cauchy_space.induced_limit_space [cauchy_space α] : limit_space α := 
{ converges := λ f x, cauchy (f ⊔ pure x),
  pure_converges := λ x, by { rw sup_idem, exact pure_cauchy x},
  le_converges := λ f g hle x hchy, le_cauchy (sup_le_sup_right hle (pure x)) hchy,
  kent_converges := by { intros, simp [sup_idem], assumption },
  sup_converges :=
  begin
    unfold converges,
    intros f g x hf hg,
    rw sup_sup_distrib_right f g (pure x),
    refine inf_sup_cauchy hf hg _,
    exact ne_bot_of_le (le_inf le_sup_right le_sup_right),
  end }

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s`. -/
def is_complete [cauchy_space α] (s : set α) := 
∀ f, cauchy f → f ≤ 𝓟 s → ∃ x ∈ s, converges f x