import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic
import category_theory.concrete_category.bundled
import deprecated.group

noncomputable theory
open set filter classical option function prod
open category_theory
open convergence_space
open_locale classical filter

-- For multiple inheritance used by cont_monoid_hom
--set_option old_structure_cmd true

universe u

variables {M G α β γ : Type*}

/-!
### Convergence semigroups, monoids, groups
-/

/-- Basic hypothesis to talk about a convergence monoid or a convergence
  semigroup. A convergence monoid over `M`, for example, is obtained by
  requiring both the instances monoid `M` and has_continuous_mul `M`. -/
class has_continuous_mul (α : Type*)
  [convergence_space α] [has_mul α] : Prop :=
(continuous_mul : continuous (uncurry (*) : α × α → α))

open has_continuous_mul

/-- Class `has_continuous_smul M α` says that the scalar multiplication
  `(•) : M → α → α` is continuous in both arguments. -/
class has_continuous_smul (M α : Type*)
  [has_scalar M α] [convergence_space M] [convergence_space α] : Prop :=
(continuous_smul : continuous (uncurry (•) : M × α → α))

open has_continuous_smul

/-- A convergence group is a group in which the multiplication and inversion
  operations are continuous. -/
class convergence_group (G : Type*)
  [convergence_space G] [group G] extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

open convergence_group

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

/-!
### Partial group actions
-/

/-- Typeclass for types with a partial scalar multiplication operation,
  denoted `·`. -/
class has_partial_scalar (M α : Type*) :=
(partial_smul : M × α → option α)

open has_partial_scalar

infixr ` · `:73 := curry has_partial_scalar.partial_smul

instance [has_partial_scalar M α] : has_scalar M (option α) :=
⟨λ a x, x.elim none (curry partial_smul a)⟩

lemma partial_smul_some [has_partial_scalar M α] : ∀ {a : M} {x : α},
  a · x = a • some x := by tauto

/-- Typeclass for partial actions by monoids. -/
class partial_mul_action (M α : Type*) [monoid M]
  extends has_partial_scalar M α :=
(identity : ∀ {x : α}, (1 : M) · x = option.some x)
(compatibility : ∀ {a b : M} {x : α}, is_some (b · x) → 
  (a * b) · x = a • (b · x))
(injective : ∀ {a : M} {x : α}, is_some (a · x) → ∀ y, a · x = a · y → x = y)

open partial_mul_action

/-- Class `has_continuous_smul M α` says that the partial scalar multiplication
  `(·) : M → α → α` is continuous in both arguments. -/
class has_continuous_partial_smul (M α : Type*) [has_partial_scalar M α]
  [convergence_space M] [convergence_space α] : Prop :=
(continuous_partial_smul : continuous (partial_smul : M × α → option α))

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

/-!
### Enveloping action
-/

def envelope (G α : Type*) [group G] [partial_mul_action G α] : G × α → G × α → Prop :=
 λ ⟨a, x⟩ ⟨b, y⟩, (b⁻¹ * a) · x = some y

namespace envelope

variables [group G] [partial_mul_action G α]

lemma is_reflexive : reflexive (envelope G α) := begin
  intros,
  unfold reflexive,
  rintro (⟨a, x⟩ : G × α),
  unfold envelope,
  simp [identity],
end

lemma is_symmetric : symmetric (envelope G α) := begin
  intros,
  unfold symmetric,
  rintro ⟨a, x⟩ ⟨b, y⟩ : G × α,
  unfold envelope,
  intro heq,
  have hsome : is_some ((b⁻¹ * a) · x), simp [heq],
  show (a⁻¹ * b) · y = some x, from calc
    (a⁻¹ * b) · y = (a⁻¹ * b) • some y : by rw partial_smul_some 
    ... = (a⁻¹ * b) • ((b⁻¹ * a) · x) : by simp [heq]
    ... = ((a⁻¹ * b) * (b⁻¹ * a)) · x : by { rw [← (compatibility hsome)]; tauto }
    ... = (1 : G) · x : by simp [mul_assoc]
    ... = some x : by exact identity
end

lemma is_transitive : transitive (envelope G α) := begin
  intros,
  unfold transitive,
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ : G × α,
  unfold envelope,
  assume heq₁ : (b⁻¹ * a) · x = some y,
  assume heq₂ : (c⁻¹ * b) · y = some z,
  have hsome₁ : is_some ((b⁻¹ * a) · x), simp *,
  have hsome₂ : is_some ((c⁻¹ * b) · y), simp *,
  show (c⁻¹ * a) · x = some z, from calc
    (c⁻¹ * a) · x = (c⁻¹ * 1 * a) · x : by simp
    ... = (c⁻¹ * b * b⁻¹ * a) · x : by simp
    ... = (c⁻¹ * b) • ((b⁻¹ * a) · x) :
      by { rw ← (compatibility hsome₁); simp [mul_assoc]; tauto }
    ... = (c⁻¹ * b) · y : by simp [partial_smul_some, heq₁]
    ... = some z : by rw heq₂
end

lemma is_equivalence : equivalence (envelope G α) := ⟨is_reflexive, is_symmetric, is_transitive⟩

instance : setoid (G × α) := 
{ r := envelope G α,
  iseqv := is_equivalence }

def quot_pure (x : α) : quot (envelope G α) := ⟦(1, x)⟧

instance : has_scalar G (G × α) := ⟨λ a ⟨b, x⟩, (a * b, x)⟩

lemma act_congr (a : G) (bx cy : G × α) (heq : bx ≈ cy) : a • bx ≈ a • cy := 
begin
  obtain ⟨b, x⟩ := bx,
  obtain ⟨c, y⟩ := cy,
  change ((a * c)⁻¹ * (a * b)) · x = some y,
  simp [mul_assoc],
  assumption,
end

lemma act_congr_sound (a : G) (bx cy : G × α) (heq : bx ≈ cy) : 
  ⟦a • bx⟧ = ⟦a • cy⟧ :=
quotient.sound (act_congr a bx cy heq)

def act_lifted (a : G) (bx : G × α) : quot (envelope G α) := ⟦a • bx⟧

instance : has_scalar G (quot (envelope G α)) :=
⟨λ a bx, quotient.lift (act_lifted a) (act_congr_sound a) bx⟩

section

variables [convergence_space G] [convergence_group G]
variables [convergence_space α]

lemma quot_pure.continuous : continuous (quot_pure : α → quot (envelope G α)) := 
begin
  set m : α → G × α := λ x, (1, x) with heq,
  have hcont : continuous m, from continuous.prod.mk 1,
  exact continuous.comp continuous_quot_mk hcont,
end

instance : has_continuous_smul G (G × α) :=
{ continuous_smul :=
  begin
    unfold continuous,
    rintro ⟨a₁, ⟨a₂, x⟩⟩ : G × (G × α),
    rintro k : filter (G × (G × α)),
    rintro hk : converges k (a₁, (a₂, x)),
    let act : G × (G × α) → G × α := uncurry has_scalar.smul,
    let mul : G × G → G := uncurry has_mul.mul,
    let rlassoc := (equiv.prod_assoc G G α).symm.to_fun,
    have heq : act = prod.map mul id ∘ rlassoc, by { funext; tidy },
    let g₁ : filter G := map fst k,
    let hg₁ : converges g₁ a₁ := hk.1,
    let g₂ : filter G := map (fst ∘ snd) k,
    let hg₂ : converges g₂ a₂ := hk.2.1,
    let f : filter α := map (snd ∘ snd) k,
    let hf : converges f x := hk.2.2,
    let g : filter (G × G) := g₁ ×ᶠ g₂,
    let a : G × G := (a₁, a₂),
    have hg : converges g a := prod.converges hg₁ hg₂,
    have : converges (map mul g) (mul a), from continuous_mul hg,
    have hconv : converges (map mul g ×ᶠ f) (mul a, x), from prod.converges this hf,
    have hle : k ≤ g₁ ×ᶠ (g₂ ×ᶠ f), from calc
      k ≤ map fst k ×ᶠ map snd k : filter.le_prod_map_fst_snd
      ... = g₁ ×ᶠ map snd k : by tauto
      ... ≤ g₁ ×ᶠ (map fst (map snd k) ×ᶠ map snd (map snd k)) :
        prod_mono (le_refl g₁) filter.le_prod_map_fst_snd
      ... = g₁ ×ᶠ (map (fst ∘ snd) k ×ᶠ map (snd ∘ snd) k) :
        by simp [filter.map_map]
      ... = g₁ ×ᶠ (g₂ ×ᶠ f) : by tauto,
    have heq' : map act (g₁ ×ᶠ (g₂ ×ᶠ f)) = map mul g ×ᶠ f, from calc
      map act (g₁ ×ᶠ (g₂ ×ᶠ f)) = map (prod.map mul id ∘ rlassoc) (g₁ ×ᶠ (g₂ ×ᶠ f)) :
        by rw heq
      ... = map (prod.map mul id) (map rlassoc (g₁ ×ᶠ (g₂ ×ᶠ f))) :
        by simp [← filter.map_map]
      ... = map (prod.map mul id) (map (equiv.prod_assoc G G α).symm (g₁ ×ᶠ (g₂ ×ᶠ f))) :
        by tauto
      ... = map (prod.map mul id) ((g₁ ×ᶠ g₂) ×ᶠ f) :
        by simp [← prod_assoc, filter.map_map]
      ... = map mul g ×ᶠ f :
        by simp [← filter.prod_map_map_eq'],
    have hle' : map act k ≤ map mul g ×ᶠ f, from eq.subst heq' (map_mono hle),
    exact le_converges hle' hconv,
  end }

end

instance
[convergence_space G] [convergence_group G]
[convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] :
has_continuous_smul G (quot (envelope G α)) :=
{ continuous_smul :=
  begin
    let act : G × (G × α) → (G × α) := uncurry (•),
    let qact : G × quot (envelope G α) → quot (envelope G α) := uncurry (•),
    let idquot : G × (G × α) → G × quot (envelope G α) := 
      prod.map id (quot.mk (envelope G α)),
    let quot_mk : G × α → quot (envelope G α) := quot.mk (envelope G α),
    have heq : qact ∘ idquot = quot_mk ∘ act, by { funext, tidy },
    have hqmap : quotient_map idquot, 
      from quotient_map.prod_map quotient_map.id quotient_map_quot_mk,
    have hcontr : continuous (quot_mk ∘ act), 
      from continuous.comp continuous_quot_mk has_continuous_smul.continuous_smul,
    have hcont : continuous qact, begin
      rw [quotient_map.continuous_iff hqmap, heq],
      assumption,
    end,
    exact hcont,
  end }

end envelope

/-!
### Adherence restrictive
-/

def adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] : Prop :=
∀ {g : filter G} {f : filter α} {a : G}, converges g a ∧ adh f = ∅ → 
   ∀ x, option.some x ∉ adh (map partial_smul (g ×ᶠ f))

def weakly_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] : Prop :=
∀ {g : filter G} {f : filter α} {a : G}, converges g a ∧ adh (map (envelope.quot_pure : α → quot (envelope G α)) f) = ∅ → 
  ∀ x, option.some x ∉ adh (map partial_smul (g ×ᶠ f))

lemma theorem5_1 {G α : Type*} [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α]
  (hcl : is_closed { x : option α | is_some x }) : 
  adh_restrictive G α :=
classical.by_contradiction 
begin
  assume hcontra : ¬ adh_restrictive G α,
  have hcontra' : ∃ (g : filter G) (f : filter α) (a : G) (x : α), 
    adh f = ∅ ∧ converges g a ∧ option.some x ∈ adh (map partial_smul (g ×ᶠ f)), 
  begin
      unfold adh_restrictive at hcontra,
      rw not_forall at hcontra,
      obtain ⟨g, rest₁⟩ := hcontra,
      rw not_forall at rest₁,
      obtain ⟨f, rest₂⟩ := rest₁,
      rw not_forall at rest₂,
      obtain ⟨a, rest₃⟩ := rest₂,
      rw not_imp at rest₃,
      obtain ⟨⟨hg, hf⟩, rest₄⟩ := rest₃,
      rw not_forall at rest₄,
      obtain ⟨x, hadh⟩ := rest₄,
      rw set.not_not_mem at hadh,
      exact ⟨g, f, a, x, hf, hg, hadh⟩,
  end,
  obtain ⟨g, f, a, x, hf, hg, hadh⟩ := hcontra',
  let h := map partial_smul (g ×ᶠ f),
  change some x ∈ adh h at hadh,
  change adheres h (some x) at hadh,
  unfold adheres at hadh,
  obtain ⟨h', hnb', hle', hconv'⟩ := hadh,
  haveI : h'.ne_bot := hnb',
  let k := map (uncurry (•)) (map has_inv.inv g ×ᶠ h'),
  cases hconv',
    case or.inl begin
      
    end,
    case or.inr : hexists begin

    end,
  sorry,
end