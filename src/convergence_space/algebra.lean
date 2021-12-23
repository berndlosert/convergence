import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic

noncomputable theory
open set filter classical option function
open_locale classical filter

class has_continuous_mul (X : Type*) [convergence_space X] [has_mul X] : Prop :=
(continuous_mul : continuous (λ p : X × X, p.1 * p.2))

class has_continuous_smul (S X : Type*) [has_scalar S X] [convergence_space S] [convergence_space X] : Prop :=
(continuous_smul : continuous (λ p : S × X, p.1 • p.2))

class convergence_group (G : Type*) [convergence_space G] [group G] extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

class partial_group_action (G X : Type*) [group G] :=
(act : G → X → option X)
(identity : ∀ {x}, act 1 x = option.some x)
(compatibility : ∀ {h} {x}, is_some (act h x) → ∀ g, act (g * h) x = act h x >>= act g)
(injective : ∀ {g} {x}, is_some (act g x) → ∀ y, act g x = act g y → x = y)

open partial_group_action

class continuous_partial_group_action
  (G X : Type*)
  [group G]
  [convergence_space G]
  [convergence_group G]
  [partial_group_action G X]
  [convergence_space X] :=
(continuity : continuous (λ p : G × X, act p.1 p.2))


def envelope (G X : Type*) [group G] [partial_group_action G X] (p p' : G × X) : Prop := uncurry act p = uncurry act p'

def phi (g h : G) (y : X) : option (quot (envelope G X)) :=
some (quot.mk (envelope G X) (g * h, y))

/-
instance {G X : Type*} [group G] [partial_group_action G X] : partial_group_action G (quot (envelope G X)) := {
  α := λ input, match input with
    | (g, none) := none
    | (g, some val) := quot.hrec_on val
      (λ ⟨h, y⟩, some (quot.mk (envelope G X) (g * h, y)))
      begin
        assume a b : G × option X,
	assume h : envelope G X a b,
	simp,
      end
    end,
  partial := sorry,
  identity := sorry,
  compatibility := sorry,
  injective := sorry,
}
-/
