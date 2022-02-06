import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic
import category_theory.concrete_category.bundled
import deprecated.group

noncomputable theory
open set filter classical option function
open category_theory
open convergence_space
open_locale classical filter

-- For multiple inheritance used by cont_monoid_hom
set_option old_structure_cmd true

universe u

-------------------------------------------------------------------------------
-- Convergence semigroups, monoids, groups
-------------------------------------------------------------------------------

/-- Basic hypothesis to talk about a convergence monoid or a convergence
  semigroup. A convergence monoid over `M`, for example, is obtained by
  requiring both the instances monoid `M` and has_continuous_mul `M`. -/
class has_continuous_mul (α : Type*)
  [convergence_space α] [has_mul α] : Prop :=
(continuous_mul : continuous (uncurry (*) : α × α → α))

/-- Class `has_continuous_smul M α` says that the scalar multiplication
  `(•) : M → α → α` is continuous in both arguments. -/
class has_continuous_smul (M α : Type*)
  [has_scalar M α] [convergence_space M] [convergence_space α] : Prop :=
(continuous_smul : continuous (uncurry (•) : M × α → α))

/-- A convergence group is a group in which the multiplication and inversion
  operations are continuous. -/
class convergence_group (G : Type*)
  [convergence_space G] [group G] extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

--structure cont_monoid_hom (M N : Type*) [mul_one_class M] [mul_one_class N] [convergence_space M] [convergence_space N] extends one_hom M N, mul_hom M N :=
--(to_fun_continuous : continuous to_fun)
--
/-
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
-/

-------------------------------------------------------------------------------
-- Partial group actions
-------------------------------------------------------------------------------

/-- Typeclass for types with a partial scalar multiplication operation,
  denoted `∙`. -/
class has_partial_scalar (M α : Type*) :=
(partial_smul : M → α → option α)
(partial_smul' : M → option α → option α := λ a x, x >>= partial_smul a)

infixr ` ∙ `:73 := has_partial_scalar.partial_smul
infixr ` ∙' `:73 := has_partial_scalar.partial_smul'

/-- Typeclass for partial actions by monoids. -/
class partial_mul_action (M α : Type*) [monoid M]
  extends has_partial_scalar M α :=
(identity : ∀ {x : α}, (1 : M) ∙ x = option.some x)
(compatibility : ∀ {a b : M} {x : α} (bx : is_some (b ∙ x)),
  (a * b) ∙ x = a ∙ option.get bx)
(injective : ∀ {a : M} {x : α}, is_some (a ∙ x) → ∀ y, a ∙ x = a ∙ y → x = y)


/-- Class `has_continuous_smul M α` says that the partial scalar multiplication
  `(∙) : M → α → α` is continuous in both arguments. -/
class has_continuous_partial_smul (M α : Type*) [has_partial_scalar M α]
  [convergence_space M] [convergence_space α] : Prop :=
(continuous_partial_smul : continuous (uncurry (∙) : M × α → option α))

/-
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
-/

-------------------------------------------------------------------------------
-- Enveloping action
-------------------------------------------------------------------------------

def envelope (G α : Type*) [group G] [partial_mul_action G α] : G × α → G × α → Prop :=
 λ ⟨a, x⟩ ⟨b, y⟩, (b⁻¹ * a) ∙ x = some y

namespace envelope

variables {G α : Type*} [group G] [partial_mul_action G α]

theorem is_reflexive : reflexive (envelope G α) := begin
  intros,
  unfold reflexive,
  rintro (⟨a, x⟩ : G × α),
  unfold envelope,
  simp [partial_mul_action.identity],
end

lemma foo (a b : G) (x : α) (b'ax : is_some ((b⁻¹ * a) ∙ x)) :
  ((a⁻¹ * b) * (b⁻¹ * a)) ∙ x = (a⁻¹ * b) ∙ option.get b'ax :=
begin
  rw (partial_mul_action.compatibility b'ax),
  tauto,
end

theorem is_symmetric : symmetric (envelope G α) := begin
  intros,
  unfold symmetric,
  rintro ⟨a, x⟩ ⟨b, y⟩ : G × α,
  unfold envelope,
  intro heq,
  have b'ax : is_some ((b⁻¹ * a) ∙ x), simp [heq],
  show (a⁻¹ * b) ∙ y = some x, from calc
    (a⁻¹ * b) ∙ y = (a⁻¹ * b) ∙ option.get b'ax :
      by simp [heq]
    ... = ((a⁻¹ * b) * (b⁻¹ * a)) ∙ x :
      by { rw [← (partial_mul_action.compatibility b'ax)]; tauto }
    ... = (1 : G) ∙ x :
      by simp [mul_assoc]
    ... = some x :
      by exact partial_mul_action.identity
end
--
--theorem is_transitive : transitive (envelope G α) := begin
--  intros,
--  unfold transitive,
--  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ : G × α,
--  unfold envelope,
--  assume heq₁ : act (b⁻¹ * a) x = some y,
--  assume heq₂ : act (c⁻¹ * b) y = some z,
--  have hsome₁ : is_some (act (b⁻¹ * a) x), simp *,
--  have hsome₂ : is_some (act (c⁻¹ * b) y), simp *,
--  show act (c⁻¹ * a) x = some z, from calc
--    act (c⁻¹ * a) x = act (c⁻¹ * 1 * a) x : by simp
--    ... = act (c⁻¹ * b * b⁻¹ * a) x : by simp
--    ... = act (b⁻¹ * a) x >>= act (c⁻¹ * b) : by rw [mul_assoc, ←(compatibility hsome₁)]
--    ... = some y >>= act (c⁻¹ * b) : by rw heq₁
--    ... = act (c⁻¹ * b) y : by simp [is_lawful_monad.pure_bind]
--    ... = some z : by rw heq₂
--end
--
--theorem is_equivalence : equivalence (envelope G α) := ⟨is_reflexive, is_symmetric, is_transitive⟩
--
--instance : setoid (G × α) := {
--  r := envelope G α,
--  iseqv := is_equivalence,
--}
--
--def quotient_map : G × α → quot (envelope G α) := λ ⟨a, x⟩, ⟦(a, x)⟧
--
--def pure (x : α) : quot (envelope G α) := ⟦(1, x)⟧
--
--def act : G → G × α → quot (envelope G α) :=
--λ a ⟨b, x⟩, ⟦(a * b, x)⟧
--
--theorem act_congr : ∀ (a : G) (p₁ p₂ : G × α) (h : p₁ ≈ p₂), envelope.act a p₁ = envelope.act a p₂ := begin
--  rintros (a : G) (⟨b₁, x₁⟩ : G × α) (⟨b₂, x₂⟩ : G × α) h,
--  unfold act,
--  simp [quotient.eq],
--  unfold has_equiv.equiv,
--  unfold setoid.r,
--  unfold envelope,
--  simp [mul_assoc],
--  assumption,
--end
--
--instance : has_scalar G (quot (envelope G α)) := {
--  smul := λ a x, quotient.lift (envelope.act a) (envelope.act_congr a) x,
--}
--
--instance
--[convergence_space G] [convergence_group G]
--[convergence_space α] [continuous_partial_group_action G α] :
--has_continuous_smul G (quot (envelope G α)) :=
--{ continuous_smul :=
--  begin
--    unfold continuous,
--    sorry,
--  end }
--
end envelope

---------------------------------------------------------------------------------
---- Adherence restrictive
---------------------------------------------------------------------------------
--
--variables {G : Type*} [group G] [convergence_space G] [convergence_group G]
--variables {α : Type*} [convergence_space α] [partial_group_action G α] [continuous_partial_group_action G α]
--
--def adh_restrictive : Prop :=
--∀ {g : filter G} {f : filter α}, adh f = ∅ → ∃ a : G, converges g a → ∀ x, option.some x ∉ adh (map (uncurry act) (g ×ᶠ f))
--
--def weakly_adh_restrictive : Prop :=
--∀ {g : filter G} {f : filter α}, adh (map (@envelope.pure G _ _ _) f) = ∅ → ∃ a : G, converges g a → ∀ x, option.some x ∉ adh (map (uncurry act) (g ×ᶠ f))
