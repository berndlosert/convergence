import algebra.group.extra
import algebra.support

variables {α G : Type*}

/-- Typeclass for partial actions of groups. -/
class partial_mul_action (G α : Type*) [group G]
  extends has_partial_scalar G α :=
(identity : ∀ (x : α), (1 : G) • x defined ∧ (1 : G) • x = x)
(compatibility : ∀ {a b : G} {x : α}, b • x defined → a • (b • x) defined →
  (a * b) • x defined ∧ (a * b) • x = a • (b • x))
(invertible : ∀ {a : G} {x y : α}, a • x defined → a • x = y → a⁻¹ • y defined ∧ x = a⁻¹ • y)

lemma partial_mul_action.injective [group G] [partial_mul_action G α]: 
  ∀ {a : G} {x y : α}, a • x defined → a • y defined → a • x = a • y → x = y :=
begin
  intros a x y hdef₁ hdef₂ heq₁,
  obtain ⟨hdef₃, heq₂⟩ := partial_mul_action.invertible hdef₁ heq₁,
  obtain ⟨hdef₄, heq₃⟩ := partial_mul_action.compatibility hdef₂ hdef₃,
  simp [(partial_mul_action.identity y).2] at heq₃,
  exact (rfl.congr (eq.symm heq₃)).mp heq₂,
end

/-!
### Enveloping action
-/

def envelope (G α : Type*) [group G] [partial_mul_action G α] : G × α → G × α → Prop :=
 λ ⟨a, x⟩ ⟨b, y⟩, (b⁻¹ * a) • x defined ∧ (b⁻¹ * a) • x = y

def envelope.embed (G : Type*) {a : Type*} [group G] [partial_mul_action G α]
  (x : α) : quot (envelope G α) := quot.mk (envelope G α) (1, x)

namespace envelope

variables [group G] [partial_mul_action G α]

lemma is_reflexive : reflexive (envelope G α) := begin
  intros,
  unfold reflexive,
  rintro (⟨a, x⟩ : G × α),
  unfold envelope,
  simp,
  exact partial_mul_action.identity x,
end

lemma is_symmetric : symmetric (envelope G α) := begin
  intros,
  unfold symmetric,
  rintro ⟨a, x⟩ ⟨b, y⟩ : G × α,
  unfold envelope,
  rintro ⟨hdef, heq⟩,
  obtain ⟨hdef', heq'⟩ := partial_mul_action.invertible hdef heq,
  simp at hdef',
  simp at heq',
  exact ⟨hdef', eq.symm heq'⟩,
end

lemma is_transitive : transitive (envelope G α) := begin
  intros,
  unfold transitive,
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ : G × α,
  unfold envelope,
  rintro ⟨hdef₁, heq₁⟩ ⟨hdef₂, heq₂⟩,
  rw [← heq₁] at hdef₂,
  rw [← heq₁] at heq₂,
  obtain ⟨hdef₃, heq₃⟩ := partial_mul_action.compatibility hdef₁ hdef₂,
  simp [mul_assoc] at hdef₃,
  simp [mul_assoc, heq₂] at heq₃,
  exact ⟨hdef₃, heq₃⟩,
end

lemma is_equivalence : equivalence (envelope G α) := ⟨is_reflexive, is_symmetric, is_transitive⟩

instance : setoid (G × α) := 
{ r := envelope G α,
  iseqv := is_equivalence }

instance : has_scalar G (G × α) := ⟨λ a ⟨b, x⟩, (a * b, x)⟩

lemma act_congr (a : G) (bx cy : G × α) (heq : bx ≈ cy) : a • bx ≈ a • cy := 
begin
  obtain ⟨b, x⟩ := bx,
  obtain ⟨c, y⟩ := cy,
  change ((a * c)⁻¹ * (a * b)) • x defined ∧ ((a * c)⁻¹ * (a * b)) • x = y,
  simp [mul_assoc],
  assumption,
end

lemma act_congr_sound (a : G) (bx cy : G × α) (heq : bx ≈ cy) : 
  ⟦a • bx⟧ = ⟦a • cy⟧ :=
quotient.sound (act_congr a bx cy heq)

def act_lifted (a : G) (bx : G × α) : quot (envelope G α) := ⟦a • bx⟧

instance : has_scalar G (quot (envelope G α)) :=
⟨λ a bx, quotient.lift (act_lifted a) (act_congr_sound a) bx⟩

end envelope