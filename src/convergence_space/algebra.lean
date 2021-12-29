import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic
import category_theory.concrete_category.bundled
import deprecated.group

noncomputable theory
open set filter classical option function open category_theory
open_locale classical filter

-- For multiple inheritance used by cont_monoid_hom
set_option old_structure_cmd true

universe u

-------------------------------------------------------------------------------
-- Convergence semigroups, monoids, groups
-------------------------------------------------------------------------------

class has_continuous_mul (X : Type*) [convergence_space X] [has_mul X] : Prop :=
(continuous_mul : continuous (λ p : X × X, p.1 * p.2))

class has_continuous_smul (S X : Type*) [has_scalar S X] [convergence_space S] [convergence_space X] : Prop :=
(continuous_smul : continuous (λ p : S × X, p.1 • p.2))

class convergence_group (G : Type*) [convergence_space G] [group G] extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

structure cont_monoid_hom (M N : Type*) [mul_one_class M] [mul_one_class N] [convergence_space M] [convergence_space N] extends one_hom M N, mul_hom M N :=
(to_fun_continuous : continuous to_fun)

structure ConvGroup :=
(carrier : Type*)
[is_group : group carrier]
[is_convergence_space : convergence_space carrier]
[is_convergence_group : convergence_group carrier]

instance (G : ConvGroup) : group G.carrier := G.is_group
instance (G : ConvGroup) : convergence_space G.carrier := G.is_convergence_space
instance : has_coe_to_sort ConvGroup Type* := ⟨ConvGroup.carrier⟩

namespace ConvGroup

structure hom (G H : ConvGroup) :=
(to_fun : G → H)
(to_fun_continuous : continuous to_fun)
(to_fun_group_hom : is_monoid_hom to_fun)

instance (G H : ConvGroup) : has_coe_to_fun (hom G H) (λ _, G → H) := ⟨hom.to_fun⟩

end ConvGroup

instance : category ConvGroup := {
  hom := ConvGroup.hom,
  comp := λ _ _ _ f g, {
    to_fun := g ∘ f,
    to_fun_continuous := sorry,
    to_fun_group_hom := sorry,
  },
  id := λ G, {
    to_fun := λ x, x,
    to_fun_continuous := sorry,
    to_fun_group_hom := sorry,
  },
}

-------------------------------------------------------------------------------
-- Partial group actions
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Enveloping action
-------------------------------------------------------------------------------

def envelope (G X : Type*) [group G] [partial_group_action G X] : G × X → G × X → Prop :=
 λ ⟨g, x⟩ ⟨h, y⟩, act (h⁻¹ * g) x = some y

variables {G : Type*} [group G]
variables {X : Type*} [partial_group_action G X]

theorem envelope_reflexive : reflexive (envelope G X) := begin
  intros,
  unfold reflexive,
  rintro (⟨g, x⟩ : G × X),
  unfold envelope,
  simp [identity],
end

theorem envelope_symmetric : symmetric (envelope G X) := begin
  intros,
  unfold symmetric,
  rintro ⟨g, x⟩ ⟨h, y⟩ : G × X,
  unfold envelope,
  intro heq,
  have heq' : is_some (act (h⁻¹ * g) x), simp [heq],
  show act (g⁻¹ * h) y = some x, from calc
    act (g⁻¹ * h) y = some y >>= act (g⁻¹ * h) : by simp [is_lawful_monad.pure_bind]
    ... = act (h⁻¹ * g) x >>= act (g⁻¹ * h) : by rw ←heq
    ... = act ((g⁻¹ * h) * (h⁻¹ * g)) x : by rw ←(compatibility heq')
    ... = act (1 : G) x : by simp [mul_assoc]
    ... = some x : by exact identity
end

theorem envelope_transitive : transitive (envelope G X) := begin
  intros,
  unfold transitive,
  rintro ⟨g, x⟩ ⟨h, y⟩ ⟨k, z⟩ : G × X,
  unfold envelope,
  assume heq₁ : act (h⁻¹ * g) x = some y,
  assume heq₂ : act (k⁻¹ * h) y = some z,
  have hsome₁ : is_some (act (h⁻¹ * g) x), simp *,
  have hsome₂ : is_some (act (k⁻¹ * h) y), simp *,
  show act (k⁻¹ * g) x = some z, from calc
    act (k⁻¹ * g) x = act (k⁻¹ * 1 * g) x : by simp
    ... = act (k⁻¹ * h * h⁻¹ * g) x : by simp
    ... = act (h⁻¹ * g) x >>= act (k⁻¹ * h) : by rw [mul_assoc, ←(compatibility hsome₁)]
    ... = some y >>= act (k⁻¹ * h) : by rw heq₁
    ... = act (k⁻¹ * h) y : by simp [is_lawful_monad.pure_bind]
    ... = some z : by rw heq₂
end

theorem envelope_equivalence : equivalence (envelope G X) := ⟨envelope_reflexive, envelope_symmetric, envelope_transitive⟩

instance : setoid (G × X) := {
  r := envelope G X,
  iseqv := envelope_equivalence,
}

def envelope_pure (x : X) : quot (envelope G X) := ⟦(1, x)⟧

def envelope_act (g : G) (hy : G × X) : option (quot (envelope G X)) :=
some (quot.mk (envelope G X) (g * hy.1, hy.2))

theorem envelope_act_congr : ∀ (g : G) (h₁y₁ h₂y₂ : G × X) (h : h₁y₁ ≈ h₂y₂), envelope_act g h₁y₁ = envelope_act g h₂y₂ := sorry

instance : partial_group_action G (quot (envelope G X)) := {
  act := λ g x, quotient.lift (envelope_act g) (envelope_act_congr g) x,
  identity := sorry,
  compatibility := sorry,
  injective := sorry,
}

variables [convergence_space G] [convergence_group G] [convergence_space X] [continuous_partial_group_action G X]

instance : continuous_partial_group_action G (quot (envelope G X)) := {
  continuity := sorry,
}
