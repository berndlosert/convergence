import algebra.group.extra
import algebra.support

open has_partial_smul

variables {α G : Type*}

/-- Typeclass for partial actions of groups. -/
class partial_mul_action (G α : Type*) [group G]
  extends has_partial_smul G α :=
(one_smul : ∀ (x : α), smul_defined 1 x ∧ (1 : G) • x = x)
(mul_smul : ∀ {a b : G} {x : α}, smul_defined b x → smul_defined a (b • x) →
  smul_defined (a * b) x ∧ (a * b) • x = a • (b • x))
(inv_smul_cancel_left : ∀ {a : G} {x y : α}, 
  smul_defined a x → a • x = y → smul_defined a⁻¹ y ∧ x = a⁻¹ • y)

export partial_mul_action

lemma partial_mul_action.injective [group G] [partial_mul_action G α]:
  ∀ {a : G} {x y : α}, smul_defined a x → smul_defined a y → a • x = a • y → x = y :=
begin
  intros a x y hdef₁ hdef₂ heq₁,
  obtain ⟨hdef₃, heq₂⟩ := inv_smul_cancel_left hdef₁ heq₁,
  obtain ⟨hdef₄, heq₃⟩ := mul_smul hdef₂ hdef₃,
  simp [(one_smul y).2] at heq₃,
  exact (rfl.congr (eq.symm heq₃)).mp heq₂,
end

/-!
### Enveloping action
-/

def envelope (G α : Type*) [group G] [partial_mul_action G α] : G × α → G × α → Prop :=
 λ ⟨a, x⟩ ⟨b, y⟩, smul_defined (b⁻¹ * a) x ∧ (b⁻¹ * a) • x = y

namespace envelope

abbreviation space (G α : Type*) [group G] [partial_mul_action G α] := quot (envelope G α)

def embed (G : Type*) {α : Type*} [group G] [partial_mul_action G α]
  (x : α) : space G α := quot.mk (envelope G α) (1, x)

variables [group G] [partial_mul_action G α]

lemma is_reflexive : reflexive (envelope G α) := 
begin
  rintro (⟨a, x⟩ : G × α),
  unfold envelope, simp,
  exact one_smul x,
end

lemma is_symmetric : symmetric (envelope G α) :=
begin
  rintro ⟨a, x⟩ ⟨b, y⟩,
  unfold envelope, rintro ⟨hdef, heq⟩,
  obtain ⟨hdef', heq'⟩ := inv_smul_cancel_left hdef heq,
  simp at *, exact ⟨hdef', eq.symm heq'⟩,
end

lemma is_transitive : transitive (envelope G α) := 
begin
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ : G × α,
  unfold envelope,
  rintro ⟨hdef₁, heq₁⟩ ⟨hdef₂, heq₂⟩,
  rw [← heq₁] at hdef₂,
  rw [← heq₁] at heq₂,
  obtain ⟨hdef₃, heq₃⟩ := mul_smul hdef₁ hdef₂,
  simp [mul_assoc] at hdef₃,
  simp [mul_assoc, heq₂] at heq₃,
  exact ⟨hdef₃, heq₃⟩,
end

lemma is_equivalence : equivalence (envelope G α) := ⟨is_reflexive, is_symmetric, is_transitive⟩

instance : setoid (G × α) := 
{ r := envelope G α,
  iseqv := is_equivalence }

instance : has_smul G (G × α) := ⟨λ a ⟨b, x⟩, (a * b, x)⟩

lemma act_congr (a : G) (bx cy : G × α) (heq : bx ≈ cy) : a • bx ≈ a • cy := 
begin
  obtain ⟨b, x⟩ := bx,
  obtain ⟨c, y⟩ := cy,
  change smul_defined ((a * c)⁻¹ * (a * b)) x ∧ ((a * c)⁻¹ * (a * b)) • x = y,
  simp [mul_assoc],
  assumption,
end

lemma act_congr_sound (a : G) (bx cy : G × α) (heq : bx ≈ cy) : 
  ⟦a • bx⟧ = ⟦a • cy⟧ :=
quotient.sound (act_congr a bx cy heq)

def act_lifted (a : G) (bx : G × α) : space G α := ⟦a • bx⟧

instance : has_smul G (space G α) :=
⟨λ a bx, quotient.lift (act_lifted a) (act_congr_sound a) bx⟩

end envelope