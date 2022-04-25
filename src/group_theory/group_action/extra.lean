import algebra.group.extra

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