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

class has_continuous_mul (α : Type*) [convergence_space α] [has_mul α] : Prop :=
(continuous_mul : continuous (uncurry (*) : α × α → α))

class has_continuous_smul (M α : Type*) [has_scalar M α] [convergence_space M] [convergence_space α] : Prop :=
(continuous_smul : continuous (uncurry (•) : M × α → α))

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
  comp := λ α Y Z f g, {
    to_fun := g ∘ f,
    to_fun_continuous := begin
      exact continuous.comp (g.to_fun_continuous) (f.to_fun_continuous),
    end,
    to_fun_group_hom := sorry,
  },
  id := λ G, {
    to_fun := λ a, a,
    to_fun_continuous := continuous_id,
    to_fun_group_hom := sorry,
  },
}

-------------------------------------------------------------------------------
-- Partial group actions
-------------------------------------------------------------------------------

class partial_group_action (G α : Type*) [group G] :=
(act : G → α → option α)
(identity : ∀ {x}, act 1 x = option.some x)
(compatibility : ∀ {b} {x}, is_some (act b x) → ∀ a, act (a * b) x = act b x >>= act a)
(injective : ∀ {a} {x}, is_some (act a x) → ∀ y, act a x = act a y → x = y)

open partial_group_action

class continuous_partial_group_action
  (G α : Type*)
  [group G]
  [convergence_space G]
  [convergence_group G]
  [convergence_space α]
  [partial_group_action G α] :=
(continuity : continuous (uncurry act : G × α → option α))

structure PartAct :=
(G α : Type*)
[group_is_group : group G]
[the_action : partial_group_action G α]

def the_group (action : PartAct) : Type* := action.G
def the_set (action : PartAct) : Type* := action.α

--instance : has_coe_to_fun (PartAct) (λ action, action.G × action.α → action.α) := ⟨action.the_action.act⟩

structure ContPartAct extends PartAct :=
[group_is_convergence_space : convergence_space G]
[group_is_convergence_group : convergence_group G]
[set_is_convergence_space : convergence_space α]
(action_is_continuous : continuous (λ p : G × α, act p.1 p.2))

-------------------------------------------------------------------------------
-- Enveloping action
-------------------------------------------------------------------------------

def envelope (G α : Type*) [group G] [partial_group_action G α] : G × α → G × α → Prop :=
 λ ⟨a, x⟩ ⟨b, y⟩, act (b⁻¹ * a) x = some y

namespace envelope

variables {G α : Type*} [group G] [partial_group_action G α]

theorem is_reflexive : reflexive (envelope G α) := begin
  intros,
  unfold reflexive,
  rintro (⟨a, x⟩ : G × α),
  unfold envelope,
  simp [identity],
end

theorem is_symmetric : symmetric (envelope G α) := begin
  intros,
  unfold symmetric,
  rintro ⟨a, x⟩ ⟨b, y⟩ : G × α,
  unfold envelope,
  intro heq,
  have heq' : is_some (act (b⁻¹ * a) x), simp [heq],
  show act (a⁻¹ * b) y = some x, from calc
    act (a⁻¹ * b) y = some y >>= act (a⁻¹ * b) : by simp [is_lawful_monad.pure_bind]
    ... = act (b⁻¹ * a) x >>= act (a⁻¹ * b) : by rw ← heq
    ... = act ((a⁻¹ * b) * (b⁻¹ * a)) x : by rw ← (compatibility heq')
    ... = act (1 : G) x : by simp [mul_assoc]
    ... = some x : by exact identity
end

theorem is_transitive : transitive (envelope G α) := begin
  intros,
  unfold transitive,
  rintro ⟨g, x⟩ ⟨h, y⟩ ⟨k, z⟩ : G × α,
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

theorem is_equivalence : equivalence (envelope G α) := ⟨is_reflexive, is_symmetric, is_transitive⟩

instance : setoid (G × α) := {
  r := envelope G α,
  iseqv := is_equivalence,
}

def quotient_map : G × α → quote (envelope G α) := λ ⟨g, x⟩, ⟦(g, x)⟧

def pure (x : α) : quot (envelope G α) := ⟦(1, x)⟧

def act : G → G × α → quot (envelope G α) :=
λ g ⟨h, y⟩, ⟦(g * h, y)⟧

theorem act_congr : ∀ (g : G) (h₁y₁ h₂y₂ : G × α) (h : h₁y₁ ≈ h₂y₂), envelope.act g h₁y₁ = envelope.act g h₂y₂ := begin
  rintros (g : G) (⟨h₁,y₁⟩ : G × α) (⟨h₂,y₂⟩ : G × α) h,
  unfold act,
  simp [quotient.eq],
  unfold has_equiv.equiv,
  unfold setoid.r,
  unfold envelope,
  simp [mul_assoc],
  assumption,
end

instance : has_scalar G (quot (envelope G α)) := {
  smul := λ g x, quotient.lift (envelope.act g) (envelope.act_congr g) x,
}

instance
[convergence_space G] [convergence_group G]
[convergence_space α] [continuous_partial_group_action G α] :
has_continuous_smul G (quot (envelope G α)) := {
  continuous_smul := begin
    unfold continuous,
    sorry,
  end,
}

end envelope

-------------------------------------------------------------------------------
-- Adherence restrictive
-------------------------------------------------------------------------------

variables {G : Type*} [group G] [convergence_space G] [convergence_group G]
variables {α : Type*} [convergence_space α] [partial_group_action G α] [continuous_partial_group_action G α]

def adh_restrictive : Prop :=
∀ {l' : filter G} {l : filter α}, adh l = ∅ → ∃ g : G, converges l' g → ∀ x, option.some x ∉ adh (map (uncurry act) (l' ×ᶠ l))

def weakly_adh_restrictive : Prop :=
∀ {l' : filter G} {l : filter α}, adh (map (@envelope.pure G _ _ _) l) = ∅ → ∃ g : G, converges l' g → ∀ x, option.some x ∉ adh (map (uncurry act) (l' ×ᶠ l))
