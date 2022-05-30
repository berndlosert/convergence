import algebra.group.defs

variables {α M : Type*}

/-!
### Partial scalar actions
-/

/-- Typeclass for partial scalar actions. `smul_defined a x` means that `a • x` is defined. -/
class has_partial_scalar (M α : Type*) extends has_scalar M α :=
(smul_defined : M → α → Prop)

export has_partial_scalar

/-- The domain of defintion of a partial action. -/
def smul_dom (M α : Type*) [has_partial_scalar M α] := { p : M × α | smul_defined p.1 p.2 }

lemma smul_dom_mem_iff [has_partial_scalar M α] {a : M} {x : α} :
  smul_defined a x ↔ (a, x) ∈ smul_dom M α := by tautology