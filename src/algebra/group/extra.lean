import algebra.group.defs

/-!
### Partial scalar actions
-/

/-- Typeclass for partial scalar actions. `smul_defined a x` means that `a • x` is defined. -/
class has_partial_scalar (M α : Type*) extends has_scalar M α :=
(smul_defined : M → α → Prop)

open has_partial_scalar

notation a ` • ` x ` defined` := smul_defined a x

/-- The domain of defintion of a partial action. -/
def smul_dom (M α : Type*) [has_partial_scalar M α] := { p : M × α | p.1 • p.2 defined }